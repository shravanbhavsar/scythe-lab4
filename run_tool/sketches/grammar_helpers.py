'''This module automates some parts of the grammar construction process.
'''

from pprint import pprint


def mk_nt(t, wrap=None, params=None):
	'''Creates a non-terminal based on the type t. If wrap is supplied,
	it wraps the non-terminal with (X nt) where X is the wrap value. This
	is useful for creating many non-terminals of the same type.
	'''
	if isinstance(t, tuple):
		nt = f"({t[0]} {' '.join([mk_nt(x) for x in t[1:]])})"
	else:
		nt = t
	if wrap is not None:
		nt = f"({wrap} {nt})"
	if params is not None:
		nt = mk_param_nt(nt, *params)
	return nt

def mk_set_nt(t):
	return mk_nt(("Set", t))

def mk_tnt(t, wrap=None, params=None):
	'''Returns a tuple of the form (nt, t) where nt is the non-terminal
	associated with the type t. If wrap is supplied, it wraps the non-terminal
	using the wrap value, producing (X nt) where X is the wrap value.
	'''
	nt = mk_nt(t, wrap=wrap, params=params)
	return (nt, t)

def mk_atom_rule(t, depends, alias=None, params=None):
	'''Creates a rule for a non-terminal associated with the type t. The rule
	maps associates the non-terminal with all dependencies of type t. If alias
	is supplied, it uses the alias as the non-terminal name. Alias is useful
	if you want to define the top-level non-terminal type manually while still
	taking advantage of the atom rule construction. 
	'''
	if alias is None:
		alias = mk_nt(t)
	if params is not None:
		alias = mk_param_nt(alias, *params)
	return [alias, t, [k for k,v in depends if v == t]]

def mk_atom_rules(depends, atom_except, atom_require=None, params=None):
	'''Constructs a standard set of atom rules based on the arguments of
	the hole's ufn. The atom_except argument is a dictionary that maps types to
	non-terminals. It is used to override the default non-terminal (type based),
	which is useful if you want to define that non-terminal manually. The
	atom_require argument is a list of types that are required to be included in
	the grammar. This is useful if some type is not a subtype of a ufn
	argument's type but is still required for the grammar to be defined.
	'''
	ts = list(set([v for k,v in depends]))
	if atom_require is not None:
		ts += atom_require
	ts = set(mk_ts_rec(ts))
	grammar = []
	for t in ts:
		alias = None
		if t in atom_except:
			alias = atom_except[t]
		if isinstance(t, tuple) and len(t) > 0 and t[0] == "Tuple":
			grammar.append(mk_tuple_rule(t, params=params))
		elif isinstance(t, tuple) and len(t) > 0 and t[0] == "Union":
			grammar.append(mk_union_rule(t, params=params))
		else:
			grammar.append(mk_atom_rule(t, depends, alias=alias, params=params))
	return grammar

def mk_tuple_rule(t, params=None):
	'''Creates a rule for a non-terminal associated with the tuple type t.
	Works best if the subtypes of the tuple type are associated with
	non-terminals using mk_atom_rule.
	'''
	tail = t[1:]
	tail = [mk_nt(x, params=params) for x in tail]
	return [*mk_tnt(t, params=params), [["tuple", *tail]]]

def mk_union_rule(t, params=None):
	'''Creates a rule for a non-terminal associated with the union type t.
	Works best if the subtypes of the union type are associated with
	non-terminals by some other means.
	'''
	head = t[0]
	tail = t[1:]
	if head != "Union":
		raise ValueError("Expected Union type")
	return [*mk_tnt(t, params=params), [mk_nt(x, params=params) for x in tail]]

def mk_ts_rec(ts):
	'''Recursively constructs a list of types from a list of types. If X is in
	the return value and x is subtype of X, then x is in the return value.
	'''
	res = []
	prim = ["Int", "Bool"]
	heads = ["Set", "Array", "Tuple", "Seq", "Union"]
	for t in ts:
		res.append(t)
		if not isinstance(t, tuple) and len(t) > 0:
			continue
		elif t[0] == "Dom":
			continue
		elif t[0] in heads:
			xs = mk_ts_rec(t[1:])
			res.extend(xs)
		else:
			raise ValueError(f"Expected one of {heads} or {prim}. Got: {t}")
	if len(res) == 0:
		raise ValueError("Empty list of types")
	return res

def mk_set_idiom(t, set_nt=None):
	'''Implements the standard idiom of updating a set of type t
	by doing nothing or adding/removing a single element of type t.
	'''
	if set_nt is None:
		set_nt = mk_set_nt(t)
	return [
		set_nt,
		["set.union", set_nt, ["set.singleton", mk_nt(t)]],
		["set.minus", set_nt, ["set.singleton", mk_nt(t)]],
	]

def mk_inf_set_idiom(set_t, wrap=None):
	nt = mk_nt(set_t, wrap=wrap)
	(_, t) = set_t
	return [*mk_tnt(set_t, wrap=wrap),
		[
			# (set_t, "emptyset"),
			["set.singleton", mk_nt(t)],
			# mk_set_nt(t),
			mk_nt(set_t),
			["set.union", nt, nt],
			["set.minus", nt, nt],
			["set.intersect", nt, nt],
		]
	]

def mk_select_idiom(arr_t, locals_nt=None, params=None):
	'''Standardizes the rule for selecting an element from an array of type
	arr_t.
	'''
	if not isinstance(arr_t, tuple) or len(arr_t) < 1 or arr_t[0] != "Array":
		raise ValueError("Expected tuple type. Got: ", arr_t)
	tail = arr_t[1:]
	if len(tail) != 2:
		raise ValueError("Expected array type of len 2. Got: ", arr_t)
	left, right = tail
	if locals_nt is None:
		left = mk_nt(left, params=params)
	else:
		left = locals_nt
	return ["select", mk_nt(arr_t, params=params), left]

def mk_store_idiom(arr_t, locals_nt=None):
	'''Implements the standard idiom of updating an array of type arr_t
	by doing nothing or updating one of its key-value pairs.
	'''
	if not isinstance(arr_t, tuple) or len(arr_t) < 1 or arr_t[0] != "Array":
		raise ValueError("Expected tuple type. Got: ", arr_t)
	tail = arr_t[1:]
	if len(tail) != 2:
		raise ValueError("Expected array type of len 2. Got: ", arr_t)
	left, right = tail
	if locals_nt is None:
		left = mk_nt(left)
	else:
		left = locals_nt
	return [
		mk_nt(arr_t),
		["store", mk_nt(arr_t), left, mk_nt(right)]]

def mk_set_store_idiom(arr_t, locals_nt=None):
	'''
	'''
	idx_t, (_, inner_set_t) = arr_t[1:]
	if locals_nt is None:
		idx_nt = mk_nt(idx_t)
	else:
		idx_nt = locals_nt
	return [
		mk_nt(arr_t),
		["store", mk_nt(arr_t), idx_nt, 
   			[
				"set.union", 
					["select", mk_nt(arr_t), idx_nt],
					["set.singleton", mk_nt(inner_set_t)]
			]],
		["store", mk_nt(arr_t), idx_nt, 
   			[
				"set.minus", 
					["select", mk_nt(arr_t), idx_nt],
					["set.singleton", mk_nt(inner_set_t)]
			]],
	]

def mk_inf_set_store_idiom(arr_t, wrap=None, locals_nt=None):
	'''
	'''
	idx_t, inner_set_t = arr_t[1:]
	if locals_nt is None:
		idx_nt = mk_nt(idx_t)
	else:
		idx_nt = locals_nt
	this_nt = mk_nt(arr_t, wrap=wrap)
	inner_set_nt_wrap = f"Helper {this_nt}"
	inner_set_nt = mk_nt(inner_set_t, wrap=inner_set_nt_wrap)
	grammar = [
		[*mk_tnt(arr_t, wrap=wrap), [
			mk_nt(arr_t),
			["store", mk_nt(arr_t), idx_nt, inner_set_nt],]
		],
		mk_inf_set_idiom(inner_set_t, wrap=inner_set_nt_wrap),
	]
	return grammar

def mk_relation_rule(op, zs, params=None):
	'''Constructs a boolean relation rule based on the operator op and the
	domains zs. The domains zs are a list of pairs of types that the relation
	should be defined between.
	'''
	nt = f"(Rel {op})"
	if params is not None:
		nt = mk_param_nt(nt, *params)
	rules = []
	for z in zs:
		left, right = z
		rule = [op, mk_nt(left, params=params), mk_nt(right, params=params)]
		rules.append(rule)
	return [nt, "Bool", rules]

def mk_eq_rule(depends, params=None):
	'''Constructs the standard equality grammar rule based on hole's
	dependencies.
	'''
	ts = set(mk_ts_rec([v for k,v in depends]))
	return mk_relation_rule("=", zip(ts, ts), params=params)

def mk_subset_rule(depends):
	'''Constructs the standard equality grammar rule based on hole's
	dependencies.
	'''
	ts = set(mk_ts_rec([v for k,v in depends]))
	ts = {t for t in ts if isinstance(t,tuple) and len(t) > 0 and t[0] == "Set"}
	return mk_relation_rule("set.subset", zip(ts, ts))

def mk_in_rule(depends, params=None):
	'''Constructs the standard set membership grammar rule based on hole's
	dependencies.
	'''
	# pprint(depends)
	ts = mk_ts_rec([v for k,v in depends])
	# pprint(ts)
	ts = set(ts)
	zs = [(t, ("Set", t)) for t in ts]
	zs = {z for z in zs if z[1] in ts}
	return mk_relation_rule("set.member", zs, params=params)

def mk_param_nt(nt, *args):
	args = (nt,) + args
	return f"({' '.join(args)})"