create table t(k integer primary key, name text, n int);
create index ti on t(n); create view v as select name, n from t;
alter table t add column extra text default 'e'; select sql from sqlite_schema where name='t';
alter table t rename column extra to more; select sql from sqlite_schema;
alter table t rename to t2; select name, tbl_name, sql from sqlite_schema;
alter table t2 drop column more; select sql from sqlite_schema where name='t2';
alter table t2 add column z int not null; alter table t2 add column y primary key; alter table t2 rename column nosuch to q;
alter table t2 drop column k;
