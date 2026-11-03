-- printf()/format(): integer conversions, flags, width, precision
select printf('%d|%i|%u|%x|%X|%o|%p', 42, -42, -1, 255, 255, 8, 255);
select printf('%5d|%-5d|%05d|%+d|% d|%+5d|%-+5d|%+05d', 42, 42, 42, 42, 42, 42, 42, -42);
select printf('%.5d|%8.5d|%-8.5d|%08.5d|%.0d|%.d', 42, 42, 42, 42, 0, 0);
select printf('%#x|%#X|%#o|%#x|%#o|%#d|%#p', 255, 255, 8, 0, 0, 7, 255);
select printf('%,d|%,d|%,d|%,d|%,u|%,x|%,010d|%,.7d', 1234567, -1234567, 999, 1000, -1, 1234567, 1234, 1);
select printf('%d|%d|%u|%x|%o', 9223372036854775807, -9223372036854775808, -9223372036854775808, -1, -1);
select printf('%ld|%lld|%lu|%lx|%li', 1, 2, 3, 255, -4);
select printf('%r|%r|%r|%r|%r|%r|%r|%r|%r|%r|%r', 0, 1, 2, 3, 4, 11, 12, 13, 21, 101, 111);
select printf('%r|%5r|%-6r|%.6r|%+r|%r', -1, 2, 3, 4, 5, 9223372036854775807);
select printf('%d %d %d', '12abc', 3.99, -3.99), printf('%d|%d|%d', '  7', 'x', x'3132');
select printf('%d|%d|%d', 1e19, -1e19, '99999999999999999999'), printf('%x', 18446744073709551615);
-- width and precision from arguments
select printf('%*d|%-*d|%*d|%.*d|%*.*d', 6, 1, 6, 2, -6, 3, 4, 4, 7, 3, 5);
select printf('%*d|', 4294967297, 5), printf('%.*f|', -3, 1.5), printf('%.*f|', 4294967298, 1.5);
select printf('%*s|%*s|%*s', NULL, 'a', 'x', 'b', 2.9, 'c');
-- missing arguments
select printf('%d|%s|%f|%c|%q|%Q|%w|%j|%J|%x|%e|%g|%r'), printf('%s %s', 'one');
-- strings
select printf('%s|%10s|%-10s|%.2s|%10.2s|%-10.2s|%.0s|%.s', 'hello', 'hello', 'hello', 'hello', 'hello', 'hello', 'hello', 'hello');
select printf('%s|%s|%s|%s|%s', 1, 2.5, NULL, x'414243', 1e100), printf('%z|%5z', 'dyn', 'z');
select printf('[%5s][%-5s][%!5s][%!-5s][%.2s][%!.2s][%!.1s]', 'é', 'é', 'é', 'é', 'éa', 'éa', '€x');
select printf('%.3s|%!.3s|%!3.1s|%!-3.2s|', '日本語テキスト', '日本語テキスト', '日本語', '日本語');
select printf('%s', 'a' || char(0) || 'b'), printf('%q', 'x' || char(0) || 'y'), length(printf('%s', x'610062'));
-- %c
select printf('%c|%c|%c|%c|%c', 'abc', 65, 'é', '€uro', '😀!');
select printf('[%5c][%-5c][%.3c][%5.3c][%-5.3c][%.0c][%.1c]', 'x', 'x', 'x', 'x', 'x', 'x', 'x');
select printf('[%5.3c][%-5.3c][%3c][%.4c]', 'é', 'é', '日', '😀');
select hex(printf('%c', NULL)), hex(printf('%c', '')), hex(printf('%3c|', NULL)), printf('%.20c', '-');
-- %q %Q %w
select printf('%q|%Q|%w', 'it''s', 'it''s', 'say "hi"'), printf('%q|%Q|%w', NULL, NULL, NULL);
select printf('%Q|%Q|%Q|%q', '', 12, 1.5, x'27');
select printf('[%10q][%-10Q][%.3q][%.3Q][%!.2Q]', 'a''b', 'a''b', 'a''bcd', 'a''bcd', 'éé''x');
select printf('%#q|%#Q|%#Q|%#q|%#w', 'a\b', 'a\b', 'tab' || char(9) || 'x\', 'nl' || char(10), 'q"' || char(1));
select printf('%#Q|%#Q', 'ctl' || char(31) || char(16) || char(1), NULL);
-- %j %J
select printf('%j|%J|%J|%j', 'a"b\c', 'a"b\c', NULL, NULL);
select printf('%J', char(8,9,10,11,12,13,1,31,32,127)), printf('%j', 'é€😀');
select printf('[%8J][%-8J][%.2J][%!.2J][%!8J][%8j][%-3J]', 'ab', 'ab', 'abcd', 'ééé', 'éé', NULL, NULL);
select printf('[%!.1j][%.1j]', 'éx', 'éx');
-- %%, %n, invalid conversions, trailing %
select printf('100%%|%5%|%-5%|%n|x', 1), printf('abc%'), printf('%'), printf('%%%');
select printf('a%yb', 1), printf('x%Tz', 1), printf('x%Sz', 1), printf('%5'), printf('%-'), printf('%.'), printf('%l'), printf('%5.3');
select printf('%5-d', 1), printf('%5 d', 1), printf('%.3-d', 1), printf('%5ld|%.3ld|%5.3ld|%*ld', 1, 2, 3, 4, 5);
select printf('é%dü%s', 1, 'ö'), printf('%d%%%d', 1, 2);
-- format argument forms
select printf(NULL), printf(NULL, 1), printf(), printf(12), printf(1.5), printf(x'2564', 7), format('%d-%s', 1, 'x');
select typeof(printf('')), printf(''), typeof(printf('%s', NULL)), printf('%s%s', NULL, NULL);
-- huge widths and precisions: SQLITE_TOOBIG
select printf('%.1000000000d', 5);
select printf('%2147483647d', 5);
select printf('%*d', -2147483647, 5);
select printf('%*d', 1000000000, 5);
select printf('%*d', -2147483648, 5), printf('%.*d', -2147483648, 5);
select printf('%9999999999d', 5), printf('%.9999999999d|', 5);
select printf('%.2000000000c', 'x');
select printf('%1000000000f', 1.0);
select printf('%.400d|', 7) = '000' || substr(printf('%.400d|', 7), 4);
select length(printf('%.400d', 7)), length(printf('%,.400d', 7)), length(printf('%1000s', 'x')), length(printf('%-1000.900c', 'é'));
