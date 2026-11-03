pragma foreign_keys=on; create table p(id integer primary key, k text unique); create table c(pid references p, pk references p(k) on delete set null, x);
insert into p values(1,'a'),(2,'b'); insert into c values(1,'a',1),(2,'b',2),(null,null,3);
insert into c values(5, null, 4); insert into c values(1,'zz',5);
delete from p where id=1; update p set id=7 where id=2; update c set pid=9 where x=2; select * from c; delete from p where k='b'; select * from c; select changes(), total_changes();
