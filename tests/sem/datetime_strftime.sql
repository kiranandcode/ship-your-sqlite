-- strftime: every specifier SQLite 3.54.1 accepts, and the ones it does not
SELECT strftime('%d|%e|%f|%F|%G|%g|%H|%k|%I|%l|%j|%J|%m|%M|%p|%P|%R|%s|%S|%T|%u|%w|%U|%V|%W|%Y|%%', '2013-10-07 08:23:19.120');
SELECT strftime('%d|%e|%f|%F|%G|%g|%H|%k|%I|%l|%j|%J|%m|%M|%p|%P|%R|%s|%S|%T|%u|%w|%U|%V|%W|%Y|%%', '2000-01-01 00:00:00');
SELECT strftime('%d|%e|%f|%F|%G|%g|%H|%k|%I|%l|%j|%J|%m|%M|%p|%P|%R|%s|%S|%T|%u|%w|%U|%V|%W|%Y|%%', '2008-12-31 23:59:59.999');
SELECT strftime('%d|%e|%f|%F|%G|%g|%H|%k|%I|%l|%j|%J|%m|%M|%p|%P|%R|%s|%S|%T|%u|%w|%U|%V|%W|%Y|%%', '-0044-03-15 12:00:00.5');
SELECT strftime('%d|%e|%f|%F|%G|%g|%H|%k|%I|%l|%j|%J|%m|%M|%p|%P|%R|%s|%S|%T|%u|%w|%U|%V|%W|%Y|%%', '9999-12-31 23:59:59.999');
SELECT strftime('%d|%e|%f|%F|%G|%g|%H|%k|%I|%l|%j|%J|%m|%M|%p|%P|%R|%s|%S|%T|%u|%w|%U|%V|%W|%Y|%%', '-4713-11-24 12:00:00');
SELECT strftime('%d|%e|%f|%F|%G|%g|%H|%k|%I|%l|%j|%J|%m|%M|%p|%P|%R|%s|%S|%T|%u|%w|%U|%V|%W|%Y|%%', '0000-01-01 12:30');
SELECT strftime('%s', '2000-01-01 00:00:00.5', 'subsec'), strftime('%s', '1960-01-01 00:00:00.5', 'subsec'), strftime('%s', '1969-12-31 23:59:59.999'), strftime('%s', '-4713-11-24 12:00', 'subsec'), strftime('%s', '9999-12-31 23:59:59.999', 'subsec');
SELECT strftime('%J', 0), strftime('%J', 0.00000001), strftime('%J', 1e-9), strftime('%J', 2451545.123456789), strftime('%J', 5373484.4999999), strftime('%J', '2000-01-01 00:00:00.001'), strftime('%J', 100), strftime('%J', 0.001);
WITH RECURSIVE g(value) AS (SELECT 0 UNION ALL SELECT value + 1 FROM g WHERE value < 23) SELECT strftime('%H %k %I %l %p %P', '2000-01-01 ' || substr('0' || value, -2) || ':05') FROM g;
WITH RECURSIVE g(value) AS (SELECT -7 UNION ALL SELECT value + 1 FROM g WHERE value < 7) SELECT strftime('%U %V %W %G %g %j %u %w', date('2000-01-01', '+' || value || ' days')) FROM g;
WITH RECURSIVE g(value) AS (SELECT 2000 UNION ALL SELECT value + 1 FROM g WHERE value < 2012) SELECT strftime('%U %V %W %G %g %j %u %w', value || '-12-28', '+' || x || ' days') FROM g JOIN (SELECT 0 AS x UNION ALL SELECT 3 UNION ALL SELECT 4 UNION ALL SELECT 6) ORDER BY value, x;
SELECT strftime('', '2000-01-01'), strftime('%', '2000-01-01'), strftime('abc%', '2000-01-01'), strftime('%q', '2000-01-01'), strftime('%C %D %h %y', '2000-01-01'), typeof(strftime('%Y')), strftime(NULL, '2000-01-01'), strftime('%Y', NULL), strftime();
SELECT strftime('plain text', '2000-01-01'), strftime('héllo %Y wörld', '2000-01-01'), strftime('%%Y', '2000-01-01'), strftime('%Y%m%d%H%M%S', '2000-01-01 01:02:03'), strftime(5, '2000-01-01'), strftime('%Y', 2451545), strftime('%Y-%m', 1700000000, 'unixepoch');
SELECT strftime('%f', '2000-01-01 00:00:59.9999'), strftime('%f', '2000-01-01 00:00:00.0005'), strftime('%f', '2000-01-01 00:00:00.0004'), strftime('%f', 2451545.0000001), strftime('%f', 2451545.000005787), strftime('%S %f', '2000-01-01 00:00:09.9995');
SELECT strftime('%F %T', '2000-02-29', '+1 year'), strftime('%Y', '-0001-01-01'), strftime('%F', '-0001-06-15'), strftime('%G %g', '-0001-01-01'), strftime('%g', '0099-12-31');
