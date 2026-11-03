create table t(a unique);
insert into t values(1);
insert into t values(2),(1),(zeroblob(1e10));
select * from t;
insert or fail into t values(3),(1),(zeroblob(1e10));
select * from t;
insert into t values(4),(zeroblob(1e10)),(1);
select * from t;
insert into t values(5),(6,7);
