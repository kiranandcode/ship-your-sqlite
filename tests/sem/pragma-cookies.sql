-- schema_version of temp and main, savepoints, rollback of cookies
create table t(a); pragma schema_version;
create index i on t(a); pragma schema_version;
insert into t values(1);
create temp table tt(x); pragma temp.schema_version; pragma schema_version;
create index ti on tt(x); pragma temp.schema_version; pragma schema_version;
create trigger tr after insert on tt begin select 1; end; pragma temp.schema_version; pragma schema_version;
create temp view tv as select 1; pragma temp.schema_version; pragma schema_version;
drop table tt; pragma temp.schema_version; pragma schema_version;
pragma temp.user_version=4; pragma temp.user_version; pragma user_version;
pragma main.user_version=3; pragma user_version;
pragma application_id=77; pragma main.application_id; pragma temp.application_id;
savepoint a; create table s(a); savepoint b; create table s2(a); rollback to b; pragma schema_version; release a; pragma schema_version;
begin; pragma user_version=9; pragma application_id=9; pragma schema_version=1000; rollback; pragma user_version; pragma application_id; pragma schema_version;
begin; pragma default_cache_size=9; rollback; pragma default_cache_size; pragma cache_size;
begin; pragma cache_size=9; rollback; pragma cache_size;
