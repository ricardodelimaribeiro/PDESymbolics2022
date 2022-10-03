(* Wolfram Language Test file *)
test = "Tests/MonomialDependenceOperatorChild.mt";
		Print["   MonomialDependenceOperator"];

label = "$Failed"
variables = Association[
	"expression" -> $Failed, 
	"result" -> $Failed
];
Get[ test ]

label = "empty";
variables = Association[{
	"expression" -> {},
    "result" -> {}
}];
Get[ test ]

label = "power and coefficient";
variables = Association[
	"expression" -> {f[x],u[x]^2,f[x] u[x]^b},
    "result" -> Piecewise[{{{b -> 0}, b == 0}}, {}],
    "depVars" -> {u},
    "indVars" -> {x},
    "pars" -> {b},
    "genFuns" -> {f}
];
Get[ test ]

label = "power and coefficient again";
variables = Association[
	"expression" -> {u[x]^2,a u[x]^b},
    "result" -> Piecewise[{{{a -> 0, b -> 2}, a == 0 && b == 2}, {{a -> 0}, a == 0}, {{b -> 2}, b == 2}}, {}],
    "depVars" -> {u},
    "indVars" -> {x},
    "pars" -> {a,b}
];
Get[ test ]

label = "power and coefficient again again";
variables = Association[
	"expression" -> {a u[x]^b},
    "result" -> Piecewise[{{{a -> 0}, a == 0}}, {}],
    "depVars" -> {u},
    "indVars" -> {x},
    "pars" -> {a,b}
];
Get[ test ]

label = "power and coefficient again again";
variables = Association[
	"expression" -> {a u[x]^b},
    "result" -> Piecewise[{{{a -> 0}, a == 0}}, {}],
    "depVars" -> {u},
    "indVars" -> {x},
    "pars" -> {a,b}
];
Get[ test ]

(*Example: 
MonomialDependence[{1, u[x]^2, a u[x]^b}, {u}, {x}, {a, b}]
*)