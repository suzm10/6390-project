
if __name__ == '__main__':
    import sys
    
    if len(sys.argv) == 2 and sys.argv[1] == "--old":
        from borrow_check_old import MyInterpreter
    elif len(sys.argv) == 2 and sys.argv[1] == "--new":
        from borrow_check_improved import MyInterpreter
    else:
        print("Please specify either --old or --new as a command line argument")
        sys.exit(1)

    print("=== simple array functionality ===")
    test = [
        ['main', [], 'returns', 'i32', [
            ('assign', 'arr', '[i32]', '[1,2,3,4,5]'),
            ('assign', 'z', 'i32', 'arr[0]'),
            ('print', 'z'),
        ]
        ]
    ]
    MyInterpreter(test, ('call', 'main', []))

    print("\n=== simple array functionality 2 ===")
    test = [
        ['main', [], 'returns', 'i32', [
            ('assign', 'arr', '[i32]', '[1,2,3,4,5]'),
            ('assign', 'z1', '&shared i32', '&shared arr[0]'),
            ('assign', 'z2', '&shared i32', '&shared arr[1]'),
            ('assign', 'z_deref', 'i32', 'deref z1'),
            ('print', 'z_deref'),
            ('return', '2')
        ]]
    ]
    MyInterpreter(test, ('call', 'main', []))

    print("\n=== multiple mutable borrows (fails) ===")
    test = [
        ['main', [], 'returns', 'i32', [
            ('assign', 'arr', '[i32]', '[1,2,3,4,5]'),
            ('assign', 'z1', '&mut i32', '&mut arr[0]'),
            ('assign', 'z2', '&mut i32', '&mut arr[0]'),
            ('return', '2') 
        ]]
    ]
    MyInterpreter(test, ('call', 'main', []))

    print("\n=== simple assignment ===")
    test = [
        ['main', ['int'], 'returns', 'i32', [
            ('assign', 'x', 'i32', 'arg0'),
            ('print', 'x'),
            ('assign', 'x', 'i32', '6'),
            ('return', 'x')
        ]]
    ]
    MyInterpreter(test, ('call', 'main', ['2']))

    print("\n=== simple type failure ===")
    test = [
        ['main', ['float'], 'returns', 'i32', [
            ('assign', 'x', 'i32', 'arg0'),
            ('return', 'x')
        ]]
    ]
    MyInterpreter(test, ('call', 'main', ['2.5']))

    print("\n=== simple scope test ===")
    test = [
        ['main', [], 'returns', 'float', [
            ('assign', 'x', 'i32', '4'),
            ('scope', [
                ('assign', 'y', 'i32', 'x'),
                ('assign', 'x', 'i32', '10'),
                ('print', 'x')
            ]),
            ('print', 'x'),
            ('return', '3.5')   
        ]]
    ]
    MyInterpreter(test, ('call', 'main', []))

    print("\n=== 'if' functionality ===")
    test = [
        ['main', [], 'returns', 'float', [
            ('assign', 'x', 'i32', '4'),
            ('assign', 'y', 'i32', '10'),
            ('if', 'x > 3', [
                ('print', 'x')
            ], [
                ('print', 'y'),
            ]),
            ('return', '3.5')
        ]]
    ]
    MyInterpreter(test, ('call', 'main', []))

    print("\n=== function calling ===")
    test = [
        ['main', [], 'returns', 'i32', [
            ('assign', 'x', 'i32', '5'),
            ('assign', 'y', 'i32', '10'),
            ('assign', 'z', 'i32', ('call', 'max', ['x', 'y'])),
            ('print', 'z'),
            ('return', '0')
            ]
        ],
        ['max', ['i32', 'i32'], 'returns', 'i32', [
            ('assign', 'a', 'i32', 'arg0'), 
            ('assign', 'b', 'i32', 'arg1'),
            ('if', 'a > b', [
                ('return', 'a')
            ], [
                ('return', 'b')
            ])
        ]]
    ]
    MyInterpreter(test, ('call', 'main', []))


    print("\n=== mutable array borrow at different indices (should pass) ===")
    test = [
        ['main', [], 'returns', 'i32', [
            ('assign', 'arr', '[i32]', '[1,2,3,4,5]'),
            ('assign', 'z1', '&mut i32', '&mut arr[0]'),
            ('assign', 'z2', '&mut i32', '&mut arr[1]'),
            ('return', '2') 
        ]]
    ]
    MyInterpreter(test, ('call', 'main', []))

    print("\n=== mutable array borrow, same indices (should fail) ===")
    test = [
        ['main', [], 'returns', 'i32', [
            ('assign', 'arr', '[i32]', '[1,2,3,4,5]'),
            ('assign', 'z1', '&mut i32', '&mut arr[0]'),
            ('assign', 'z2', '&mut i32', '&mut arr[0]'),
            ('return', '2') 
        ]]
    ]
    MyInterpreter(test, ('call', 'main', []))


    print("\n=== regular borrow check (shared aliasing allowed) ===")
    test = [
        ['main', [], 'returns', 'i32', [
            ('assign', 'x', 'i32', '5'),
            ('assign', 'y1', '&shared i32', '&shared x'),
            ('assign', 'y2', '&shared i32', '&shared x'),
            ('return', '2') 
        ]]
    ]
    MyInterpreter(test, ('call', 'main', []))

    print("\n=== regular borrow check (mutable aliasing disallowed) ===")
    test = [
        ['main', [], 'returns', 'i32', [
            ('assign', 'x', 'i32', '5'),
            ('assign', 'y1', '&mut i32', '&mut x'),
            ('assign', 'y2', '&mut i32', '&mut x'),
            ('return', '2')
        ]]
    ]
    MyInterpreter(test, ('call', 'main', []))
