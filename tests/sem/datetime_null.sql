-- NULL arguments, storage classes, numbers vs text, values from tables
CREATE TABLE t(a, b TEXT, c REAL, d INTEGER);
INSERT INTO t VALUES ('2000-01-01', '2451545', 2451545, 2451545), (NULL, NULL, NULL, NULL), (2451545.5, '2000-06-01 12:00', 1700000000, 1700000000), (X'41', 'junk', -1, 0);
SELECT date(a), date(b), date(c), date(d), datetime(c, 'unixepoch'), datetime(d, 'auto'), julianday(a), typeof(julianday(a)), unixepoch(b), typeof(unixepoch(b)) FROM t;
SELECT typeof(date(b)) FROM t;
SELECT date(a, b) FROM t;
SELECT datetime('2000-01-01', c || ' days') FROM t;
SELECT unixepoch('2000-01-01', 'subsec'), typeof(unixepoch('2000-01-01', 'subsec')), unixepoch(0), unixepoch(2451545), typeof(unixepoch(2451545.5)), unixepoch(2451545.5, 'subsec');
SELECT date(2451545, 1.5), date('2000-01-01', 1.5e0), datetime('2000-01-01', CAST('+1 day' AS BLOB)), datetime('2000-01-01', X'2B31206461792B'), date(1.5e300), date(-0.0), date(9223372036854775807), date(-9223372036854775808);
SELECT date('2000-01-01', '+1 day' || char(0) || 'junk'), date('2000-01-01' || char(0) || 'junk'), strftime('%Y' || char(0) || '%m', '2000-01-01');
