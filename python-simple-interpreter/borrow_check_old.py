class MyInterpreter:
    def __init__(self, program, call_expr):
        self.program = program
        self.functions = self._parse_functions(program)
        self.call_expr = call_expr
        
        # Type check first
        if self._type_check():
            # If type check passes, execute
            result = self._execute(call_expr)
            if result is not None:
                print(f"Program returned: {result}")
        
    def _parse_functions(self, program):
        funcs = {}
        for func_def in program:
            name = func_def[0]
            param_types = func_def[1]
            return_type = func_def[3]
            body = func_def[4]
            funcs[name] = {
                'param_types': param_types,
                'return_type': return_type,
                'body': body
            }
        return funcs
    
    def _type_check(self):
        try:
            # Type check the call expression
            if self.call_expr[0] != 'call':
                raise Exception(f"Invalid call expression")
            
            func_name = self.call_expr[1]
            args = self.call_expr[2]
            
            if func_name not in self.functions:
                raise Exception(f"Function '{func_name}' not found")
            
            func = self.functions[func_name]
            
            # Check argument count
            if len(args) != len(func['param_types']):
                raise Exception(f"Function '{func_name}' expects {len(func['param_types'])} arguments, got {len(args)}")
            
            # Check argument types
            for i, (arg, expected_type) in enumerate(zip(args, func['param_types'])):
                arg_type = self._infer_literal_type(arg)
                if not self._types_compatible(arg_type, expected_type):
                    raise Exception(f"Argument {i} type mismatch: expected {expected_type}, got {arg_type}")
            
            # Type check function body
            self._type_check_function(func_name)
            
            print("Type checking passed!")
            return True
            
        except Exception as e:
            print(f"Type error: {e}")
            return False
    
    def _type_check_function(self, func_name):
        func = self.functions[func_name]
        env = {}
        borrow_tracker = BorrowTracker()
        
        # Add parameters to environment
        for i, param_type in enumerate(func['param_types']):
            env[f'arg{i}'] = self._normalize_type(param_type)
        
        # Type check body
        return_type = self._type_check_statements(func['body'], env, borrow_tracker, func['return_type'])
        
        return return_type
    
    def _type_check_statements(self, statements, env, borrow_tracker, expected_return_type):
        for stmt in statements:
            if stmt[0] == 'assign':
                var_name = stmt[1]
                var_type = self._normalize_type(stmt[2])
                value_expr = stmt[3]
                
                # Infer the type of the value expression
                value_type = self._infer_type(value_expr, env)
                
                # Check for borrow creation
                if var_type.startswith('&'):
                    self._check_borrow(value_expr, var_type, env, borrow_tracker)
                
                # Check type compatibility
                if not self._types_compatible(value_type, var_type):
                    raise Exception(f"Type mismatch in assignment to '{var_name}': expected {var_type}, got {value_type}")
                
                env[var_name] = var_type
                
            elif stmt[0] == 'print':
                var_name = stmt[1]
                if var_name not in env:
                    raise Exception(f"Variable '{var_name}' not found")
                    
            elif stmt[0] == 'return':
                return_value = stmt[1]
                return_type = self._infer_type(return_value, env)
                if not self._types_compatible(return_type, expected_return_type):
                    raise Exception(f"Return type mismatch: expected {expected_return_type}, got {return_type}")
                    
            elif stmt[0] == 'scope':
                # Create new scope with copy of environment
                new_env = env.copy()
                new_borrow_tracker = borrow_tracker.enter_scope()
                self._type_check_statements(stmt[1], new_env, new_borrow_tracker, expected_return_type)
                # Don't propagate variables from inner scope
                
            elif stmt[0] == 'if':
                cond = stmt[1]
                then_block = stmt[2]
                else_block = stmt[3] if len(stmt) > 3 else []
                
                # Validate condition is a boolean expression
                self._validate_condition(cond, env)
                
                # Type check blocks
                self._type_check_statements(then_block, env.copy(), borrow_tracker.enter_scope(), expected_return_type)
                if else_block:
                    self._type_check_statements(else_block, env.copy(), borrow_tracker.enter_scope(), expected_return_type)
        
        return None
    
    def _check_borrow(self, value_expr, borrow_type, env, borrow_tracker):
        is_mut = '&mut' in borrow_type
        
        # Extract the variable being borrowed
        borrowed_var = self._extract_borrowed_var(value_expr)
        
        if borrowed_var:
            borrow_tracker.add_borrow(borrowed_var, is_mut)
    
    def _validate_condition(self, cond, env):
        cond_str = str(cond).strip()
        
        # Check for comparison operators
        operators = ['==', '!=', '>', '<', '>=', '<=']
        has_operator = any(op in cond_str for op in operators)
        
        if not has_operator:
            raise Exception(f"Invalid condition: '{cond}' - must be a comparison expression")
        
        # Extract operands and validate they exist in environment
        for op in operators:
            if op in cond_str:
                parts = cond_str.split(op)
                if len(parts) == 2:
                    left = parts[0].strip()
                    right = parts[1].strip()
                    
                    # Check that variables exist
                    if left in env:
                        pass  # Variable exists
                    elif not self._is_literal(left):
                        raise Exception(f"Variable '{left}' not found in condition")
                    
                    if right in env:
                        pass  # Variable exists
                    elif not self._is_literal(right):
                        raise Exception(f"Variable '{right}' not found in condition")
                break
    
    def _is_literal(self, expr):
        expr = str(expr).strip()
        try:
            float(expr)
            return True
        except:
            return False
    
    def _extract_borrowed_var(self, expr):
        expr = str(expr).strip()
        
        # Handle &shared arr[0] or &mut arr[0]
        if '&shared' in expr or '&mut' in expr:
            # Remove the & and shared/mut prefix
            if '&shared' in expr:
                expr = expr.replace('&shared', '').strip()
            elif '&mut' in expr:
                expr = expr.replace('&mut', '').strip()
            
            # Extract base variable (before [)
            if '[' in expr:
                return expr.split('[')[0].strip()
            return expr
        
        return None
    
    def _infer_type(self, expr, env):

        # Handle tuple expressions (like function calls)
        if isinstance(expr, tuple):
            if expr[0] == 'call':
                func_name = expr[1]
                if func_name not in self.functions:
                    raise Exception(f"Function '{func_name}' not found")
                return self.functions[func_name]['return_type']
            return 'unit'
        


        expr_str = str(expr).strip()
        
        # Handle deref
        if expr_str.startswith('deref '):
            var_name = expr_str[6:].strip()
            if var_name not in env:
                raise Exception(f"Variable '{var_name}' not found")
            var_type = env[var_name]
            # Remove reference
            if var_type.startswith('&'):
                return var_type.split(' ')[-1]
            raise Exception(f"Cannot deref non-reference type '{var_type}'")
        
        # Handle array indexing
        if '[' in expr_str and ']' in expr_str and not expr_str.startswith('['):
            # Check if this is part of a borrow expression
            if '&shared' not in expr_str and '&mut' not in expr_str:
                var_name = expr_str.split('[')[0].strip()
                if var_name not in env:
                    raise Exception(f"Variable '{var_name}' not found")
                var_type = env[var_name]
                if var_type.startswith('[') and var_type.endswith(']'):
                    return var_type[1:-1]  # Return element type
                raise Exception(f"Cannot index non-array type '{var_type}'")
        
        # Handle borrow expressions
        if '&shared' in expr_str or '&mut' in expr_str:
            # Extract the actual expression being borrowed
            if '&shared' in expr_str:
                actual_expr = expr_str.replace('&shared', '').strip()
                borrow_kind = 'shared'
            else:
                actual_expr = expr_str.replace('&mut', '').strip()
                borrow_kind = 'mut'
            
            # Get the type of what's being borrowed
            borrowed_type = self._infer_type(actual_expr, env)
            
            # Return reference type
            return f'&{borrow_kind} {borrowed_type}'
        
        # Variable reference
        if expr_str in env:
            return env[expr_str]
        
        # Literal type inference
        return self._infer_literal_type(expr)
    
    def _infer_literal_type(self, value):
        value_str = str(value).strip()
        
        # Array literal
        if value_str.startswith('[') and value_str.endswith(']'):
            if '.' in value_str:
                return '[f32]'
            return '[i32]'
        
        # Numeric literal
        if '.' in value_str:
            return 'f32'
        
        try:
            int(value_str)
            return 'i32'
        except:
            pass
        
        return 'unit'
    
    def _normalize_type(self, type_str):
        mapping = {
            'int': 'i32',
            'float': 'f32',
            '[int]': '[i32]',
            '[float]': '[f32]'
        }
        return mapping.get(type_str, type_str)
    
    def _types_compatible(self, actual, expected):
        actual = self._normalize_type(str(actual))
        expected = self._normalize_type(str(expected))
        return actual == expected
    
    def _execute(self, call_expr):
        if call_expr[0] != 'call':
            raise Exception("Invalid call expression")
        
        func_name = call_expr[1]
        args = call_expr[2]
        
        return self._execute_function(func_name, args)
    
    def _execute_function(self, func_name, args):
        func = self.functions[func_name]
        env = {}


        # Bind arguments
        for i, arg in enumerate(args):
            # If arg is already evaluated, use it directly
            if isinstance(arg, (int, float, list)):
                env[f'arg{i}'] = arg
            else:
                env[f'arg{i}'] = self._eval_expr(arg, env)
        
        
        # Execute body
        result = self._execute_statements(func['body'], env)
        return result
    
    def _execute_statements(self, statements, env):
        for stmt in statements:
            if stmt[0] == 'assign':
                var_name = stmt[1]
                value_expr = stmt[3]
                env[var_name] = self._eval_expr(value_expr, env)
                
            elif stmt[0] == 'print':
                var_name = stmt[1]
                print(env[var_name])
                
            elif stmt[0] == 'return':
                return_value = stmt[1]
                return self._eval_expr(return_value, env)
                
            elif stmt[0] == 'scope':
                # Create new scope
                new_env = env.copy()
                result = self._execute_statements(stmt[1], new_env)
                if result is not None:
                    return result
                    
            elif stmt[0] == 'if':
                cond = stmt[1]
                then_block = stmt[2]
                else_block = stmt[3] if len(stmt) > 3 else []
                # Evaluate condition
                if self._eval_condition(cond, env):
                    result = self._execute_statements(then_block, env.copy())
                    if result is not None:
                        return result
                elif else_block:
                    result = self._execute_statements(else_block, env.copy())
                    if result is not None:
                        return result
        
        return None
    
    def _eval_expr(self, expr, env):


        # Handle tuple expressions (like function calls)
        if isinstance(expr, tuple):
            if expr[0] == 'call':
                func_name = expr[1]
                args = expr[2]
                # Evaluate arguments
                eval_args = [self._eval_expr(arg, env) for arg in args]
                # Execute the function
                return self._execute_function(func_name, eval_args)
            return None
        

        expr_str = str(expr).strip()
        
        # Handle deref
        if expr_str.startswith('deref '):
            var_name = expr_str[6:].strip()
            ref_value = env[var_name]
            return ref_value  # In our implementation, refs store actual values
        
        # Handle array indexing (but not within borrow expressions)
        if '[' in expr_str and ']' in expr_str and not expr_str.startswith('['):
            if '&shared' not in expr_str and '&mut' not in expr_str:
                var_name = expr_str.split('[')[0].strip()
                index_str = expr_str.split('[')[1].split(']')[0].strip()
                index = int(index_str)
                return env[var_name][index]
        
        # Handle borrow expressions - store the actual value
        if '&shared' in expr_str or '&mut' in expr_str:
            # Extract the actual expression being borrowed
            if '&shared' in expr_str:
                actual_expr = expr_str.replace('&shared', '').strip()
            else:
                actual_expr = expr_str.replace('&mut', '').strip()
            return self._eval_expr(actual_expr, env)
        
        # Variable reference
        if expr_str in env:
            return env[expr_str]
        
        # Array literal
        if expr_str.startswith('[') and expr_str.endswith(']'):
            content = expr_str[1:-1]
            if not content:
                return []
            elements = [x.strip() for x in content.split(',')]
            if '.' in content:
                return [float(x) for x in elements]
            return [int(x) for x in elements]
        
        # Numeric literal
        if '.' in expr_str:
            return float(expr_str)
        
        try:
            return int(expr_str)
        except:
            return expr_str
    
    def _eval_condition(self, cond, env):
        cond_str = str(cond).strip()
        
        # Handle comparison operators
        operators = [('==', lambda a, b: a == b),
                     ('!=', lambda a, b: a != b),
                     ('>=', lambda a, b: a >= b),
                     ('<=', lambda a, b: a <= b),
                     ('>', lambda a, b: a > b),
                     ('<', lambda a, b: a < b)]
        
        for op_str, op_func in operators:
            if op_str in cond_str:
                parts = cond_str.split(op_str)
                if len(parts) == 2:
                    left = self._eval_expr(parts[0].strip(), env)
                    right = self._eval_expr(parts[1].strip(), env)
                    return op_func(left, right)
        
        return False


class BorrowTracker:
    def __init__(self):
        self.borrows = {}  # var_name -> list of borrow types ('mut' or 'shared')
    
    def add_borrow(self, var_name, is_mut):
        if var_name not in self.borrows:
            self.borrows[var_name] = []
        
        current_borrows = self.borrows[var_name]
        
        if is_mut:
            # Cannot have mutable borrow if any other borrows exist
            if current_borrows:
                raise Exception(f"Cannot create mutable reference to '{var_name}': already borrowed")
            self.borrows[var_name].append('mut')
        else:
            # Cannot have shared borrow if mutable borrow exists
            if 'mut' in current_borrows:
                raise Exception(f"Cannot create shared reference to '{var_name}': already mutably borrowed")
            self.borrows[var_name].append('shared')
    
    def enter_scope(self):
        new_tracker = BorrowTracker()
        new_tracker.borrows = self.borrows.copy()
        return new_tracker
