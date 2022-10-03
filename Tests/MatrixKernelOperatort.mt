(* Wolfram Language Test file *)
	test = "Tests/MatrixKernelOperatorChild.mt";
		Print["   MatrixKernelOperator"];


label = "1-9 matrix"
template = Association[
	"variables" -> Association[
		(*"indVars" -> {x}, 
  		"depVars" -> {u}*)
  	], 
  	"operator" -> MatrixKernelOperator, 
  	"expression" -> {{1,2,3},{4,5,6},{7,8,9}},
  	"result" -> {{1, -2, 1}}
]
Get[test]

label = "pars"
template = Association[
	"variables" -> Association[
		"pars" -> {a, b}(*"indVars" -> {x}, 
  		"depVars" -> {u}*)
  	], 
  	"operator" -> MatrixKernelOperator, 
  	"expression" -> {{a, 0}, {0, b}},
  	"result" -> Piecewise[{{{}, a != 0 && b != 0}, {{{0, 1}}, a != 0 && b == 0}, {{{1, 0}}, a == 0 && b != 0}, {{{1, 0}, {0, 1}}, a == 0 && b == 0}}, $Failed]
]
Get[test]

label = "pars and indVars"
template = Association[
	"variables" -> Association[
		"pars" -> {a,b},
		"indVars" -> {x} 
  		(*"depVars" -> {u}*)
  	], 
  	"operator" -> MatrixKernelOperator, 
  	"expression" -> {{a x, 0}, {2 x, b x}},
  	"result" -> Piecewise[{{{}, a != 0 && b != 0 && x != 0}, {{{-b/2, 1}}, a == 0 || (b != 0 && x == 0)}, {{{0, 1}}, a != 0 && b == 0}}, $Failed]
]
Get[test]

label = "1-9 matrix"
template = Association[
	"variables" -> Association[
		(*"indVars" -> {x}, 
  		"depVars" -> {u}*)
  	], 
  	"operator" -> MatrixKernelOperator, 
  	"expression" -> {{1,2,3},{4,5,6},{7,8,9}},
  	"result" -> {}
]
Get[test]

label = "1-9 matrix"
template = Association[
	"variables" -> Association[
		(*"indVars" -> {x}, 
  		"depVars" -> {u}*)
  	], 
  	"operator" -> MatrixKernelOperator, 
  	"expression" -> {{1,2,3},{4,5,6},{7,8,9}},
  	"result" -> {}
]
Get[test]

