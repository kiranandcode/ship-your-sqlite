create table s(g text, v int); insert into s values ('a',3),('a',1),('b',5),('a',2),('b',5),('c',null);
select g, v, row_number() over (partition by g order by v) from s;
select g, v, sum(v) over (order by v desc), count(*) over () from s;
select v, sum(v) over w, avg(v) over w from s window w as (order by v groups between 1 preceding and current row exclude current row);
select g, max(v), rank() over (order by max(v)) from s group by g;
