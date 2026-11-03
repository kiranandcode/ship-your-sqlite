-- round(): (i64)(r +- 0.5) for 0 digits, else %!.*f read back
select round(2.5), round(-2.5), round(0.5), round(-0.5), round(0.49999999999999994), round(-0.49999999999999994);
select round(1.005, 2), round(2.675, 2), round(1.0005, 3), round(99.995, 2), round(0.125, 2), round(0.375, 2);
select round(0.1 + 0.7, 1), round(1.45, 1), round(1.55, 1), round(-1.45, 1), round(1234.5678, 2), round(1234.5678, -2);
select round(3.14159265358979, 10), round(3.14159265358979, 15), round(3.14159265358979, 16), round(3.14159265358979, 30), round(3.14159265358979, 31);
select round(0.1, 17), round(0.1, 20), round(1.0/3, 17), round(2.0/3, 16), round(12.5, 15), round(0.3, 16);
select round(4503599627370496.5), round(4503599627370495.5), round(4503599627370497.0, 2), round(-4503599627370495.5), round(1e20, 3), round(-1e300, 2);
select round(1e-300, 2), round(-1e-300, 2), round(5e-324, 30), round(1e-5, 4), round(1e-5, 5), round(-0.001, 2);
select round(123), round('2.5'), round('abc'), round(NULL), round(1.5, NULL), round(2.567, '1'), round(2.567, 1.9);
select round(x, 2), round(x, 1), round(x) from (with recursive g(value) as (select -20 union all select value + 1 from g where value < 20) select value / 8.0 as x from g);
select round(x, 3) from (with recursive g(value) as (select 1 union all select value + 1 from g where value < 30) select value * 0.0005 as x from g);
select round(1e999), round(-1e999, 2), typeof(round(5));
-- quote() of a REAL: %!0.17g
select quote(0.1), quote(1.0), quote(-0.0), quote(1e999), quote(-1e999), quote(0.1 + 0.2), quote(1e100), quote(1e-5);
select quote(123456789012345678.0), quote(1.7976931348623157e308), quote(5e-324), quote(2.5e-308), quote(49.47), quote(100.0);
with recursive g(x) as (select -3 union all select x + 1 from g where x < 3) select quote(x / 7.0) from g;
select quote(round(2.675, 2)), quote(round(1e-300, 2));
