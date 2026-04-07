(* Wolfram Language Test file *)
	test = FileNameJoin[{DirectoryName[$TestFileName], "MatrixInverseOperatorChild.mt"}];
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

label = "piecewise matrix from documentation"
template = <|
	"variables" -> <|
		"pars" -> {a},
		"generators" -> {x},
		"facts" -> True
	|>,
	"expression" -> Piecewise[
		{
			{{{0, 0, 2}, {0, 1 + x, 2}, {0, 0, 1}}, a == 1},
			{{{0, 0, 2}, {0, -1 + x, 2}, {0, 0, 1}}, a == -1},
			{{{(a^2 - 1) x, 0, 2}, {0, a + x, 2}, {0, 0, 1}}, a^2 != 1}
		},
		$Failed
	],
	"result" -> Piecewise[
		{
			{$Failed, a^2 == 1},
			{{{1/((a^2 - 1) x), 0, -2/((a^2 - 1) x)}, {0, 1/(a + x), -2/(a + x)}, {0, 0, 1}}, True}
		},
		$Failed
	]
|>
Get[test]

label = "piecewise matrix with default branch from documentation"
template = <|
	"variables" -> <|
		"pars" -> {a},
		"generators" -> {x},
		"facts" -> True
	|>,
	"expression" -> Piecewise[
		{
			{{{0, 0, 2}, {0, 1 + x, 2}, {0, 0, 1}}, a == 1},
			{{{0, 0, 2}, {0, -1 + x, 2}, {0, 0, 1}}, a == -1}
		},
		{{(a^2 - 1) x, 0, 2}, {0, a + x, 2}, {0, 0, 1}}
	],
	"result" -> Piecewise[
		{
			{$Failed, a^2 == 1},
			{{{1/((a^2 - 1) x), 0, -2/((a^2 - 1) x)}, {0, 1/(a + x), -2/(a + x)}, {0, 0, 1}}, True}
		},
		$Failed
	]
|>
Get[test]
