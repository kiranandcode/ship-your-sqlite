#!/usr/bin/env python3
"""Random differential tests for the JSON functions.

    python3 -I experiments/json/gen.py SEED N [--nest] > script.sql

Each statement is preceded by `select 'MARK <k>';` so that outputs can be
compared statement by statement (experiments/json/rand.sh). Documents are
random JSON values rendered as canonical JSON, JSON5 variants, occasionally
mutated into malformed text, or converted to JSONB; paths are drawn from the
document's own structure plus malformed ones; calls cover every JSON
function, `->`/`->>`, the jsonb_ forms, json_each/json_tree and the
aggregates. `--nest` also nests edit functions inside other JSON functions
(this exercises json.c's per-statement parse cache, see Sql/Json.lean).
"""
import random
import sys

KEYS = ["a", "b", "c", "k1", "a b", "é", "", "x\"y", "1", "$k", "_z", "a.b", "CamelKey", "a\\b", "tab\tk"]
STRS = ["", "x", "hello world", "q\"uote", "back\\slash", "nl\nline", "é ü", "中文", "😀", "ctl\x01\x1f",
        "slash/", "it's", "[1,2]", "{\"a\":1}", "123", "true", "null", " 1"]


def sql_str(s):
    return "'" + s.replace("'", "''") + "'"


def json_str(s, r, json5=False):
    out = []
    for ch in s:
        o = ord(ch)
        if ch == '"':
            out.append('\\"')
        elif ch == '\\':
            out.append('\\\\')
        elif o < 0x20:
            m = {8: '\\b', 9: '\\t', 10: '\\n', 12: '\\f', 13: '\\r'}
            if json5 and r.random() < 0.3:
                out.append('\\x%02x' % o)
            else:
                out.append(m.get(o, '\\u%04x' % o))
        elif o > 0x7f and r.random() < 0.3 and o < 0x10000:
            out.append('\\u%04x' % o)
        elif ch == '/' and r.random() < 0.3:
            out.append('\\/')
        else:
            out.append(ch)
    body = ''.join(out)
    if json5 and r.random() < 0.3 and "'" not in s:
        return "'" + body + "'"
    return '"' + body + '"'


def rand_num(r):
    k = r.random()
    if k < 0.3:
        return r.choice(["0", "1", "-1", "42", "-0", "100"])
    if k < 0.5:
        return str(r.randint(-10**6, 10**6))
    if k < 0.6:
        return r.choice(["9223372036854775807", "-9223372036854775808", "9223372036854775808",
                         "18446744073709551616", "99999999999999999999", "-9223372036854775809"])
    if k < 0.8:
        return r.choice(["1.5", "-0.25", "0.1", "3.141592653589793", "1e10", "1E-5", "-2.5e+3",
                         "1.0", "0.0", "123456789.123456789", "1e308", "1e-320", "1e400", "5e-324"])
    return "%d.%de%d" % (r.randint(0, 999), r.randint(0, 999), r.randint(-30, 30))


def rand_value(r, depth=0):
    k = r.random()
    if depth < 4 and k < 0.25:
        return ("arr", [rand_value(r, depth + 1) for _ in range(r.randint(0, 4))])
    if depth < 4 and k < 0.5:
        keys = r.sample(KEYS, r.randint(0, 4))
        if r.random() < 0.1 and keys:
            keys.append(keys[0])  # duplicate label
        return ("obj", [(kk, rand_value(r, depth + 1)) for kk in keys])
    if k < 0.65:
        return ("str", r.choice(STRS))
    if k < 0.85:
        return ("num", rand_num(r))
    return ("lit", r.choice(["true", "false", "null"]))


def render(v, r, json5=False):
    t, x = v
    ws = (lambda: r.choice(["", " ", "\n", "\t", " /*c*/ "] if json5 else ["", " ", "\n"])) if r.random() < 0.3 else (lambda: "")
    if t == "arr":
        items = [ws() + render(e, r, json5) + ws() for e in x]
        trail = "," if (json5 and x and r.random() < 0.3) else ""
        return "[" + ",".join(items) + trail + "]"
    if t == "obj":
        items = []
        for kk, e in x:
            if json5 and kk and all(c.isalnum() or c in "_$" for c in kk) and not kk[0].isdigit() and r.random() < 0.5:
                ks = kk
            else:
                ks = json_str(kk, r, json5)
            items.append(ws() + ks + ws() + ":" + ws() + render(e, r, json5) + ws())
        trail = "," if (json5 and x and r.random() < 0.3) else ""
        return "{" + ",".join(items) + trail + "}"
    if t == "str":
        return json_str(x, r, json5)
    if t == "num":
        if json5 and r.random() < 0.3:
            return r.choice(["0x1F", "-0xff", "+7", ".5", "5.", "-.25", "Infinity", "-Infinity", "NaN", "0XABCDEF",
                             "0x8000000000000000", "0xFFFFFFFFFFFFFFFFF"])
        return x
    return x


def paths_of(v, prefix="$"):
    out = [prefix]
    t, x = v
    if t == "arr":
        for i, e in enumerate(x):
            out += paths_of(e, "%s[%d]" % (prefix, i))
        if x:
            out.append("%s[#-%d]" % (prefix, 1))
        out.append(prefix + "[#]")
    elif t == "obj":
        for kk, e in x:
            if kk and all(c.isalnum() or c == "_" for c in kk):
                out += paths_of(e, prefix + "." + kk)
            else:
                out += paths_of(e, prefix + '."' + kk.replace('"', '\\"') + '"')
    return out


def rand_path(r, v):
    k = r.random()
    ps = paths_of(v)
    if k < 0.7:
        p = r.choice(ps)
        if r.random() < 0.3:
            p += r.choice([".new", "[0]", ".a.b", "[#]", '."q k"', "[5]", "[#-1]"])
        return p
    return r.choice(["$", "$.zz", "$[9]", "$[#-9]", "x", "$.", "$[", "$a", "$.a[", "$[#+1]", '$."unterminated',
                     "$[-1]", "$.a.b.c", "$[0][0]", "$ ", "$[1x]", "$..a"])


def sql_val(r, doc_sql=None):
    k = r.random()
    if k < 0.15:
        return str(r.randint(-100, 100))
    if k < 0.25:
        return r.choice(["1.5", "-0.0", "1e300*1e300", "0.1+0.2", "2.0", "1e-7"])
    if k < 0.45:
        return sql_str(r.choice(STRS))
    if k < 0.5:
        return "null"
    if k < 0.6:
        return "json(%s)" % sql_str(r.choice(['[1,2]', '{"x":1}', '"s"', '3', 'null', '{"a":[true]}']))
    if k < 0.65:
        return "jsonb(%s)" % sql_str(r.choice(['[1,2]', '{"x":1}', '"s"', '3', '{"a":"b"}']))
    if k < 0.7:
        return "json_array(%s)" % ", ".join(sql_val(r) for _ in range(r.randint(0, 2)))
    if k < 0.75:
        return "json_object('k', %s)" % sql_val(r)
    if k < 0.8:
        return "json_quote(%s)" % sql_val(r)
    if k < 0.85:
        return r.choice(["x'00'", "x'0b'", "x'ff'", "x'1331'", "x''"])
    if k < 0.9 and doc_sql:
        return "%s -> %s" % (doc_sql, sql_str(r.choice(["$.a", "$[0]", "a", "$"])))
    if k < 0.95:
        return "json_extract(%s, '$.a')" % sql_str(r.choice(['{"a":[1]}', '{"a":"s"}', '{"a":2}', '{"a":{"b":1}}']))
    return "case when %d then json('[%d]') else 'x' end" % (r.randint(0, 1), r.randint(0, 9))


def mutate(s, r):
    if not s:
        return "x"
    i = r.randrange(len(s))
    k = r.random()
    if k < 0.4:
        return s[:i] + s[i + 1:]
    if k < 0.7:
        return s[:i] + r.choice(["x", ",", "]", "}", ":", '"', "\\", "'", "/", "*", " ", "0", "."]) + s[i:]
    return s[:i]


def rand_doc(r):
    v = rand_value(r)
    k = r.random()
    if k < 0.55:
        txt = render(v, r, False)
    elif k < 0.85:
        txt = render(v, r, True)
    else:
        txt = mutate(render(v, r, r.random() < 0.5), r)
    sql = sql_str(txt)
    if r.random() < 0.2:
        sql = "jsonb(%s)" % sql
    return v, sql


EDITS = ["json_set", "json_insert", "json_replace", "json_array_insert",
         "jsonb_set", "jsonb_insert", "jsonb_replace", "jsonb_array_insert"]


def rand_call(r, nest):
    v, d = rand_doc(r)
    if nest and r.random() < 0.3:
        e = r.choice(["json_set", "json_insert", "json_replace", "json_remove", "json_patch"])
        if e == "json_remove":
            d = "json_remove(%s, %s)" % (d, sql_str(rand_path(r, v)))
        elif e == "json_patch":
            d = "json_patch(%s, %s)" % (d, sql_str(render(rand_value(r), r)))
        else:
            d = "%s(%s, %s, %s)" % (e, d, sql_str(rand_path(r, v)), sql_val(r))
    p = lambda: sql_str(rand_path(r, v))
    k = r.randrange(24)
    if k == 0:
        return "select json(%s), json_type(%s);" % (d, d)
    if k == 1:
        return "select hex(jsonb(%s));" % d
    if k == 2:
        return "select json_extract(%s, %s);" % (d, ", ".join(p() for _ in range(r.randint(1, 3))))
    if k == 3:
        return "select quote(jsonb_extract(%s, %s));" % (d, ", ".join(p() for _ in range(r.randint(1, 2))))
    if k == 4:
        arg = r.choice([p(), str(r.randint(-3, 5)), sql_str(r.choice(KEYS)), "'[0]'"])
        return "select %s -> %s, %s ->> %s;" % (d, arg, d, arg)
    if k == 5:
        return "select json_type(%s, %s), json_array_length(%s, %s);" % (d, p(), d, p())
    if k == 6:
        return "select json_valid(%s, %d), json_error_position(%s);" % (d, r.choice([1, 2, 3, 4, 5, 6, 8, 9, 10]), d)
    if 7 <= k <= 10:
        e = r.choice(EDITS)
        args = ", ".join("%s, %s" % (p(), sql_val(r, d)) for _ in range(r.randint(1, 3)))
        f = "%s(%s, %s)" % (e, d, args)
        return "select quote(%s);" % f
    if k == 11:
        e = r.choice(["json_remove", "jsonb_remove"])
        return "select quote(%s(%s, %s));" % (e, d, ", ".join(p() for _ in range(r.randint(0, 3))))
    if k == 12:
        v2, d2 = rand_doc(r)
        e = r.choice(["json_patch", "jsonb_patch"])
        return "select quote(%s(%s, %s));" % (e, d, d2)
    if k == 13:
        ind = r.choice(["", ", '  '", ", ''", ", null", ", '\t'"])
        return "select json_pretty(%s%s);" % (d, ind)
    if k == 14:
        return "select json_quote(%s), json_array(%s, %s), json_object('k', %s, %s, %s);" % (
            sql_val(r, d), sql_val(r, d), sql_val(r, d), sql_val(r, d), sql_str(r.choice(KEYS)), sql_val(r, d))
    if k == 15:
        return "select quote(jsonb_array(%s)), quote(jsonb_object(%s, %s));" % (
            ", ".join(sql_val(r, d) for _ in range(r.randint(0, 3))), sql_str(r.choice(KEYS)), sql_val(r, d))
    if k in (16, 17):
        fn = r.choice(["json_each", "json_tree", "jsonb_each", "jsonb_tree"])
        root = (", " + p()) if r.random() < 0.4 else ""
        return "select * from %s(%s%s);" % (fn, d, root)
    if k == 18:
        vals = ", ".join("(%s, %s)" % (sql_str(r.choice(KEYS)) if r.random() < 0.85 else "null", sql_val(r)) for _ in range(r.randint(0, 4)))
        if not vals:
            return "select json_group_array(1), json_group_object('a', 1) where 0;"
        return "select json_group_array(v), json_group_object(k, v), quote(jsonb_group_array(v)), quote(jsonb_group_object(k, v)) from (select column1 k, column2 v from (values %s));" % vals
    if k == 19:
        return "select json_array(%s), json_object('d', %s);" % (d, d)
    if k == 20:
        return "select json_array_length(%s), json_type(%s);" % (d, d)
    if k == 21:
        e = r.choice(EDITS)
        return "select quote(json(%s(%s, %s, %s)));" % (e, d, p(), sql_val(r, d))
    if k == 22:
        return "select json_set(%s, '$', %s);" % (d, sql_val(r, d))
    return "select quote(json_extract(%s, %s)), typeof(%s ->> %s);" % (d, p(), d, p())


def main():
    seed = int(sys.argv[1])
    n = int(sys.argv[2])
    nest = "--nest" in sys.argv
    r = random.Random(seed)
    out = sys.stdout
    for i in range(n):
        out.write("select 'MARK %d';\n" % i)
        out.write(rand_call(r, nest) + "\n")


main()
