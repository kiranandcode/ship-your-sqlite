-- pragmas on a fresh connection: page_size, auto_vacuum, encoding before the
-- database is written
pragma page_size=8192; pragma page_size; create table t(a); pragma page_size;
pragma encoding; pragma encoding='UTF-16'; pragma encoding; pragma encoding='utf16le'; pragma encoding; select 'x';
