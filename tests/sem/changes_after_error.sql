create table t(a);
insert into t values(1),(2);
select abs(-9223372036854775807-1);
select changes();
create table t(a);
select changes();
insert into t values(1),(2);
insert into t select abs(-9223372036854775807-1);
select changes();
