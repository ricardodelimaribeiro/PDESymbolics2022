(* Wolfram Language Test file *)

test = "Tests/CleanNullLagrangiansOperatorChild.mt";
		Print["   CleanNullLagrangiansOperator"];

variables = Association[
	"MonList" -> $Failed, 
	"result" -> $Failed
	];

label = "$Failed"
Get[ test ]

variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"MonList" -> {u[x]^2, u[x] u'[x], u'[x]^2, u[x] u''[x], u[x] u'''[x]},
	"result" -> {u[x]^2, Derivative[1][u][x]^2, u[x]*Derivative[2][u][x]}
}];
label = "first list"

Get[ test ]

variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"MonList" -> {u'[x]v[x]+u[x]v'[x]},
	"result" -> {}
}];
label = "One Null lagrangian"

Get[ test ]

variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"MonList" -> {H[u'[x]] u''[x], H'[u'[x]] u''[x]^2},
	"result" -> {Derivative[1][H][Derivative[1][u][x]]*Derivative[2][u][x]^2}
}];
label = "Generic Function"

Get[ test ]

variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a},
	"MonList" -> {u[x]^a, u[x]^2},
	"result" -> {u[x]^a, u[x]^2}
}];
label = "Parameter"

Get[ test ]



(*Operator = " with VariationalDOperator"

variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"VarDOperator" -> VariationalDOperator,
	"MonList" -> {u[x]^2, u[x] u'[x], u'[x]^2, u[x] u''[x], u[x] u'''[x]},
	"result" -> {u[x]^2, Derivative[1][u][x]^2, u[x]*Derivative[2][u][x]}
}];
label = "first list"
label = label <> Operator

Get[ test ]

variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"VarDOperator" -> VariationalDOperator,
	"MonList" -> {u'[x]v[x]+u[x]v'[x]},
	"result" -> {}
}];
label = "One Null lagrangian"
label = label <> Operator

Get[ test ]

variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"VarDOperator" -> VariationalDOperator,
	"MonList" -> {H[u'[x]] u''[x], H'[u'[x]] u''[x]^2},
	"result" -> {Derivative[1][H][Derivative[1][u][x]]*Derivative[2][u][x]^2}
}];
label = "Generic Function"
label = label <> Operator

Get[ test ]

variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"VarDOperator" -> VariationalDOperator,
	"pars" -> {a},
	"MonList" -> {u[x]^a, u[x]^2},
	"result" -> {u[x]^a, u[x]^2}
}];
label = "Parameter"
label = label <> Operator

Get[ test ]*)


