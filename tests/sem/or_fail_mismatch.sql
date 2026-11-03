create table t0(c0 integer primary key);
insert or fail into t0 values (95), (-1e308);
select * from t0;
insert or fail into t0 values (1), ('a');
select * from t0;
create table t1(a unique);
insert or fail into t1 values (1), (2), (1), (3);
select * from t1;
select changes();
