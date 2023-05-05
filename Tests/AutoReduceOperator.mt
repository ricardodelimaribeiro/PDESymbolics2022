(* Wolfram Language Test file *)

test = "Tests/AutoReduceOperatorChild.mt";
		Print["   Template"];


label = "unitary"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> AutoReduceOperator, 
  	"expression" -> {},
  	"result" -> {}
]
Get[test]

label = "Length 2"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> AutoReduceOperator, 
  	"expression" -> {0},
  	"result" -> {}
]
Get[test]

label = "Length 3"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> AutoReduceOperator, 
  	"expression" -> {1},
  	"result" -> {1}
]
Get[test]

label = "Length 4"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> AutoReduceOperator, 
  	"expression" -> {a},
  	"result" -> (*{1}*)Piecewise[{{{1}, a != 0}, {{}, a == 0}}, $Failed]
]
Get[test]

label = "Length 5"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> AutoReduceOperator, 
  	"expression" -> {$Failed},
  	"result" -> $Failed
]
Get[test]


label = "Length 6"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> AutoReduceOperator, 
  	"expression" -> {$Failed, u[x]},
  	"result" -> $Failed
]
Get[test]


label = "Length 7"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> AutoReduceOperator, 
  	"expression" -> {a u[x]^2, u[x]},
  	"result" -> {u[x]}
]
Get[test]

label = "Length 8"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> AutoReduceOperator, 
  	"expression" -> {a u[x]^2, u[x],a},
  	"result" -> (*{1}*)Piecewise[{{{1}, a != 0}, {{u[x]}, a == 0}}, $Failed]
]
Get[test]

label = "Length 9"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u,v},
  		"pars"-> {a}
  	], 
  	"operator" -> AutoReduceOperator, 
  	"expression" -> {a u[x]^2, v[x]},
  	"result" -> (*{a u[x]^2, v[x]}*)Piecewise[{{{v[x], u[x]^2}, a != 0}, {{v[x]}, a == 0}}, $Failed]
]
Get[test]