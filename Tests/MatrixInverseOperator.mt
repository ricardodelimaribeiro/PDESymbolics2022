(* Wolfram Language Test file *)
	test = "Tests/MatrixInverseOperatorChild.mt";
		Print["   MatrixInverseOperator"];


label = "Identity"
template = Association[
	"variables" -> Association[
  	"pars"->{},
  	"generators"->{},
  	"facts"->True], 
  	"operator" -> MatrixInverseOperator, 
  	"expression" -> {{1,0},{0,1}},
  	"result" -> {{1,0},{0,1}}
  	
]
Get[test]

label = "1,2,3,4 matrix"
template = <|
	"variables" -> <|"pars"->{},"generators"->{},
  	"facts"->True|>,
	"expression" -> {{1, 2}, {3, 4}},
	"result" -> {{-2, 1}, {3/2, -(1/2)}}

|>
Get[test]

label = "one parameter"
template = <|
	"variables" -> <|  	"generators"->{},
  	"facts"->True,
"pars"->{a}|>,
	"expression" -> {{1, 0}, {0, a}},
	"result" -> Piecewise[{{{{1, 0}, {0, a^(-1)}}, a != 0}}, $Failed]

|>
Get[test]
(*TODO include more from documentation*)