(* Wolfram Language Test file *)
	test = "Tests/GrobOpChild.mt";
		Print["   ComprehensiveGroebnerSystemOperator"];


label = "empty"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> ComprehensiveGroebnerSystemOperator, 
  	"expression" -> {},
  	"result" -> {}
]
Get[test]

label = "{1}"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x}
		],
	"operator" -> ComprehensiveGroebnerSystemOperator,
	"expression" -> {1},
   "result" -> {1}
]
Get[test]

label = "has one"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x}
		],
	"operator" -> ComprehensiveGroebnerSystemOperator,
	"expression" -> {1, u[x]},
   "result" -> {1}
]
Get[test]

label = "has zero and a constant, without generators"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x}
		],
	"operator" -> ComprehensiveGroebnerSystemOperator,
	"expression" -> {9,0},
   "result" -> {9}
]
Get[test]

label = "has zero and a constant, with generators"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x},
		"generators" -> {u[x],x}
		],
	"operator" -> ComprehensiveGroebnerSystemOperator,
	"expression" -> {9,0},
   "result" -> {1}
]
Get[test]

label = "has zeros"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x}
		],
	"operator" -> GrobOp,
	"expression" -> Sequence[{u[x],0},{}],
   "result" -> {u[x]}
]
Get[test]

label = "square is too much"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x}
		],
	"operator" -> ComprehensiveGroebnerSystemOperator,
	"expression" -> {u[x],u[x]^2},
   "result" -> {u[x]}
]
(*Get[test]*)

label = "from GroebnerBasis documentation Degree Lex"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x},
		"ordering" -> (*MonomialOrder*) DegreeLexicographic,
		"generators" -> {u[x], u'[x]}
		],
	"operator" -> ComprehensiveGroebnerSystemOperator,
	"expression" -> {u'[x]^2 - 2 u[x]^2, u'[x] u[x] - 3},
   
   "result" -> {-3 + u[x]*Derivative[1][u][x], 2*u[x]^2 - Derivative[1][u][x]^2, -6*u[x] + Derivative[1][u][x]^3}
]
Get[test]

label = "from GroebnerBasis documentation Lex"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x}, 
		"ordering" -> Lexicographic
		],
	"operator" -> ComprehensiveGroebnerSystemOperator,
	"expression" -> {u'[x]^2 - 2 u[x]^2, u'[x] u[x] - 3},
	(*MonomialOrder -> Lexicographic*)
   "result" -> {-18 + Derivative[1][u][x]^4, 6*u[x] - Derivative[1][u][x]^3}
]
Get[test]

(*Sometimes it is safe to use "reduce"->Reduce from the start.*)
label = "piecewise result four segments and $Failed"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x},
		"pars" -> {a},
		"reduce"->Reduce
		],
	"operator" -> ComprehensiveGroebnerSystemOperator,
	"expression" -> {u'[x]^2 - u[x]^2, u[x] + a u'[x]},
   "result" -> Piecewise[
 List[List[
   List[Plus[Times[Power[a, -1], u[x]], Derivative[1][u][x]], 
    Power[u[x], 2]], Unequal[Power[a, 3], a]], 
  List[List[Plus[Times[-1, u[x]], Derivative[1][u][x]]], 
   Equal[a, -1]], 
  List[List[Plus[u[x], Derivative[1][u][x]]], Equal[a, 1]], 
  List[List[Power[Derivative[1][u][x], 2], u[x]], 
   Equal[a, 0]]], $Failed]
]
Get[test]

(*TODO get more examples that work.....*)
