-- JSON5 input accepted by json() and friends, and json_valid flags
select json('{a:1, $b_2:2, _c:3}'), json('{''single'':''quotes''}'), json('[1,2,3,]'), json('{"a":1,}');
select json('[0x1F, -0xff, +5, .5, 5., -.5, +.5e3, 1e5, 0x0, 0XaB]');
select json('[Infinity, -Infinity, +Infinity, inf, -inf, NaN, QNaN, SNaN, nan, infinity, INF, -INFINITY]');
select json('[-NaN]');
select json('[infx]');
select json('[-infinit]');
select json('[1, /* comment */ 2, // line comment
 3]');
select json(char(0xa0) || '[1]'), json('[1' || char(0x2028) || ',2]'), json(char(0xfeff) || '1');
select json('"\x41\v\0\''"'), json('''a"b'''), json('"line1\
line2"');
select json('"tab	inside"');
select json('{"a":1} '), json(' {"a":1}'), json('{"a":1}  /* c */ ');
select json('[0xFFFFFFFFFFFFFFFF]'), json('[0x10000000000000000]'), json('[-0x8000000000000000]');
select jsonb('[0x1F, .5, 5., +3, Infinity, NaN]'), jsonb('{a:1}'), jsonb('''x''');
select jsonb('"\x41"'), jsonb('"a\''b"'), jsonb('"\v"');
select json(jsonb('"\x41\v\0\''"')), json(jsonb('[.5, 5., -.5, -5.]'));
select json('{ab:1}'), jsonb('{ab:1}'), json('{ab:1}');
select json('{ab /*c*/ : 1}'), json('{"a"/*c*/:1}'), json('[1/*c*/,2]');
select json_valid('{a:1}'), json_valid('{a:1}', 1), json_valid('{a:1}', 2), json_valid('{a:1}', 3), json_valid('{"a":1}', 1);
select json_valid('[1,]'), json_valid('[1,]', 2), json_valid('0x1F'), json_valid('0x1F', 2);
select json_valid('x'), json_valid('x', 2), json_valid(''), json_valid(null), json_valid(123), json_valid(1.5), json_valid('  [1]  ');
select json_valid(jsonb('[1]')), json_valid(jsonb('[1]'), 4), json_valid(jsonb('[1]'), 8), json_valid(jsonb('[1]'), 12), json_valid(jsonb('[1]'), 6);
select json_valid(x'ff', 4), json_valid(x'ff', 8), json_valid(x'5b315d', 1), json_valid(x'5b315d', 4), json_valid(x'5b315d', 8);
select json_valid(x'13', 8), json_valid(x'1339', 8), json_valid(x'2341', 8), json_valid(x'0c', 8), json_valid(x'1c00', 8);
select json_valid(x'00', 8), json_valid(x'10', 8), json_valid(x'01', 8), json_valid(x'02', 4);
select json_valid('[1]', 0);
select json_valid('[1]', 16);
select json_valid('[1]', -1);
select json_valid('[1]', '3'), json_valid('{a:1}', 2.9), json_valid(null, 1);
select json_valid(null, 99);
