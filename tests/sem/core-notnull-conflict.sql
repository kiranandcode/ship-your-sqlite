create table t(a not null default 7, b not null, c); insert into t values(1,2,3),(4,5,6);
update or ignore t set b = null where a = 1; select * from t;
update or replace t set a = null where a = 4; select * from t;
update or replace t set b = null; select * from t;
update t set a = null; insert or replace into t values(null, 9, 9); insert or ignore into t values(1, null, 1); select * from t;
update or fail t set b = case when a = 7 then null else b end; select * from t;
