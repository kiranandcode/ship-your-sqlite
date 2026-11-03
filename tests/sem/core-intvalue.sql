select '1e2' | 0, '1.9' | 0, '1e2' << 1, ~'1e2', substr('abcdef', '2e0'), zeroblob('2e1') = zeroblob(2), hex(char('6.6e1')), round(1.23456, '2e0'), abs('1e2'), ~1.9, ~'x';
