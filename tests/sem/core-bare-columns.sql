create table t(g, v); insert into t values(1,'a'),(2,'x'),(1,'b'),(1,'c'),(2,'y');
select g, group_concat(v), v from t group by g;
select group_concat(v), v from t;
create index ti on t(g); select g, group_concat(v), v from t group by g;
