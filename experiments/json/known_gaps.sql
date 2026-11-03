-- Known differences between Sql.Json (as wired into the evaluator) and SQLite.
-- Run with experiments/json/dt.sh; each statement below is expected to differ.

-- 1. json.c's per-statement parse cache: an edit function's output text of
--    >= 100 bytes (or containing a rendered hex integer) is cached with the
--    *edited* blob; a later jsonb_* call on that text in the same statement
--    returns that blob (TEXTRAW nodes, widened headers) instead of a fresh
--    parse. Sql.Json.scalarCached models the cache; the evaluator calls the
--    cache-free scalar?.
select jsonb(json_set('{"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa":1,"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb":2}', '$.c', 'x"y'));

-- 2. The `value` column of json_each/json_tree carries the JSON subtype for
--    arrays and objects; a column reference gives exprIsJson nothing to go on.
select json_array(value) from json_each('[[1]]');

-- 3. json_each/json_tree columns are computed lazily in SQLite: rows before a
--    column error are output, and an unselected column never errors. The
--    tableFn? interface returns all rows or one error.
select * from json_tree('[0xFFFFFFFFFFFFFFFFF]');
select key from json_each('[0xFFFFFFFFFFFFFFFFF]');

-- 4. Value-dependent subtypes approximated statically (see Sql/Json.lean):
--    an extracted *string* that is itself canonical JSON is embedded raw.
select json_array(json_extract('["123"]', '$[0]'));
select json_array(coalesce(null, '[1]'), coalesce(json_extract('{}', '$.a'), '[2]'));

-- 5. Arity errors are prepare-time in SQLite (even with no rows) and use the
--    name as written; here they arise per call with the lower-case name.
select JSON_TYPE('[1]', '$', 1);
select json_type('[1]', '$', 1) from (select 1 where 0);
