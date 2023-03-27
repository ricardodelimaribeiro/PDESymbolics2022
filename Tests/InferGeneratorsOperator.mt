(* Wolfram Language Test file *)

test = "Tests/InferGeneratorsOperatorChild.mt";
		Print["   Template"];


label = "unitary"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> InferGeneratorsOperator, 
  	"expression" -> u[x]^2,
  	"result" -> {u[x]}
]
Get[test]

label = "length 2"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> InferGeneratorsOperator, 
  	"expression" -> u[x]^2 u'[x] u[x],
  	"result" -> {Derivative[1][u][x], u[x]}
]
Get[test]

label = "length 3"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> InferGeneratorsOperator, 
  	"expression" -> {},
  	"result" -> {}
]
Get[test]

label = "length 4"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> InferGeneratorsOperator, 
  	"expression" -> {0},
  	"result" -> {}
]
Get[test]

label = "length 5"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> InferGeneratorsOperator, 
  	"expression" -> {c},
  	"result" -> {}
]
Get[test]

label = "length 6"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u,v}
  	], 
  	"operator" -> InferGeneratorsOperator, 
  	"expression" -> {u'[x]^2, a v'[x]},
  	"result" -> (*{Derivative[1][v][x], Derivative[1][u][x]}*) {Derivative[1][u][x], Derivative[1][v][x]} 
]
Get[test]

label = "length 6 again"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> InferGeneratorsOperator, 
  	"expression" -> $Failed,
  	"result" -> $Failed
]
Get[test]

label = "length 7"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u},
  		"VarDOperator"->DVarDOperator
  	], 
  	"operator" -> InferGeneratorsOperator, 
  	"expression" -> {u[x+1]+u[x]},
  	"result" -> {u[x+1],u[x]}
]
(*TODO need to code something for the discrete case!!!  we will need to check what we have in Friedemann's part of the code.
Get[test]*)