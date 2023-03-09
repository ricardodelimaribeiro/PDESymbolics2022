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