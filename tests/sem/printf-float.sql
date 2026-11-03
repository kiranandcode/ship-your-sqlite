-- printf() float conversions: %f %e %E %g %G with every flag
select printf('%f|%e|%E|%g|%G', 3.14159265358979, 3.14159265358979, 3.14159265358979, 3.14159265358979, 3.14159265358979);
select printf('%f|%e|%g', 0.0, 0.0, 0.0), printf('%f|%e|%g|%+f|% e', -0.0, -0.0, -0.0, -0.0, -0.0);
select printf('%.0f|%.0f|%.0f|%.0f|%.0f|%.0f', 0.5, 1.5, 2.5, -0.5, 0.49999999999999994, 9.5);
select printf('%.1f|%.2f|%.2f|%.2f|%.3f|%.2f', 0.05, 0.005, 1.005, 2.675, 1.0005, 99.995);
select printf('%.20f|%.30f|%!.20f|%!.30f', 0.1, 0.1, 0.1, 0.1);
select printf('%.15f|%!.15f|%!.15f|%!.16f', 12.5, 12.5, 0.3, 0.3);
select printf('%f|%f|%.3f|%.10f', 1e20, 1e-20, 123456789.987654321, 2.0/3);
select printf('%f', 1e308), printf('%.0f', 1.7976931348623157e308);
select printf('%e|%.0e|%#.0e|%.3e|%.20e|%!.20e|%E', 12345.678, 12345.678, 12345.678, 12345.678, 12345.678, 12345.678, 1e-300);
select printf('%e|%e|%e|%e', 5e-324, 2.2250738585072014e-308, 1.7976931348623157e308, 1e100);
select printf('%g|%g|%g|%g|%g|%g|%g', 100000, 1000000, 1e-4, 1e-5, 123456789, 0.0001234, 1e15);
select printf('%.3g|%.10g|%.17g|%.20g|%!.17g|%!.20g|%.0g|%#.0g', 3.14159, 3.14159, 0.1, 0.1, 0.1, 0.1, 25, 25);
select printf('%#g|%#.3g|%#g|%!g|%!.3g|%!g|%!g', 1.0, 1.0, 100000, 1.0, 1.0, 1e100, 0.5);
select printf('%G|%G|%#G', 1e-10, 1e20, 1.5);
-- !: 20 significant digits instead of 16, and the round-trip shortening at 17
select printf('%.17g|%!.17g|%.17e|%!.16e|%!.16e', 49.47, 49.47, 49.47, 49.47, 0.30000000000000004);
select printf('%!.17g|%!.17g|%!.17g|%!.17g', 0.1 + 0.7, 1e23, 9.999999999999999e22, 123456789012345678);
select printf('%!.15g|%!.15g|%!.18g|%!.19g|%!.25f', 0.1, 1.0/3, 1.0/3, 1.0/3, 1.0/3);
select printf('%.16g|%.18g|%.25g|%.40f', 1.0/3, 1.0/3, 1.0/3, 1.0/3);
-- width, zero padding, signs, alternate forms
select printf('[%10f][%-10.2f][%010.2f][%+010.2f][% 010.2f][%+.2f][% .2f]', 3.5, 3.5, -3.5, 3.5, 3.5, 3.5, 3.5);
select printf('[%15e][%-15e][%015e][%+e][%015g][%-15g|]', 1.5, 1.5, -1.5, 1.5, -1.5, 1.5);
select printf('[%#.0f][%#f][%#.2f][%#.2f][%#+.2f][%#.2e]', 3.0, 3.0, -0.001, -0.009, -0.001, -0.001);
select printf('[%.2f][%.0f][%#.0f][%.1e]', -0.001, -0.4, -0.4, -0.0);
-- thousands separator on floats
select printf('%,f|%,.2f|%,.0f|%,f|%,f|%,g|%,e', 1234567.891, 1234567.891, 999.5, 100.0, -1234.5, 1234567.0, 1234567.0);
select printf('%,f|%,.1f|%,012.1f', 1e20, 123.45, 1234.5);
-- infinities (zero padding shows 9.0e+999)
select printf('%f|%e|%g|%+f|% g|%10f|%-10e|', 1e999, -1e999, 1e999, 1e999, 1e999, 1e999, -1e999);
select printf('%010g|%010e|%!010g|%0.3e', 1e999, -1e999, 1e999, 1e999);
select length(printf('%010f', 1e999)), substr(printf('%010f', -1e999), 1, 12);
-- precision limits and default
select printf('%.f|%.e|%.g', 2.5, 2.5, 2.5);
select length(printf('%.400f', 1.0)), length(printf('%.400e', 1.0)), printf('%.400g', 0.1), printf('%.350f', 1e-320) = '0.' || substr(printf('%.350f', 1e-320), 3);
select printf('%!.400f', 1e-320);
-- argument conversions to double
select printf('%f|%f|%f|%f|%f|%f', '3.5', '1e3x', 'abc', NULL, 7, x'31');
select printf('%e|%g', '  -2.5e-3  ', 9223372036854775807);
-- many random-ish values
select printf('%.15g|%.16g|%.17g|%!.15g|%!.16g|%!.17g', x, x, x, x, x, x) from (with recursive g(value) as (select 1 union all select value + 1 from g where value < 12) select 0.1 * value as x from g);
select printf('%.3f|%.2e|%g', x, x, x) from (with recursive g(value) as (select -5 union all select value + 1 from g where value < 5) select value / 7.0 as x from g);
