(* Wolfram Language Test file *)

test = "Tests/LeadingTermOperatorChild.mt";
		Print["   Template"];


label = "unitary"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingTermOperator, 
  	"expression" -> u'[x]^2,
  	"result" -> Derivative[1][u][x]^2
]
Get[test]

label = "Length 1"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingTermOperator, 
  	"expression" -> 0,
  	"result" -> 0
]
Get[test]

label = "Length 2"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingTermOperator, 
  	"expression" -> a u'[x] + b u[x] + c ,
  	"result" -> Piecewise[{{a Derivative[1][u][x], a != 0}, {b u[x], 
   a == 0 && b != 0}, {c, a == 0 && b == 0 && c != 0}, {0, 
   a == 0 && b == 0 && c == 0}, {$Failed, True}}]
]
Get[test]

label = "Length 3"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u,v}
  	], 
  	"operator" -> LeadingTermOperator, 
  	"expression" -> a u'[x] + b v'[x] + c ,
  	"result" -> Piecewise[{{a*Derivative[1][u][x], a != 0}, {b*Derivative[1][v][x], a == 0 && b != 0}, {c, a == 0 && b == 0 && c != 0}, {0, a == 0 && b == 0 && c == 0}}, $Failed]
]
Get[test]

label = "Length 4"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingTermOperator, 
  	"expression" -> $Failed,
  	"result" -> $Failed
]
Get[test]

label = "Length 5"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingTermOperator, 
  	"expression" -> c,
  	"result" -> Piecewise[{{c, c != 0}, {0, c == 0}, {$Failed, True}}]
]
Get[test]

label = "Length 6"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingTermOperator, 
  	"expression" -> 1,
  	"result" -> 1
]
Get[test]


label = "Length 7"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingTermOperator, 
  	"expression" -> u'[x] + a u[x],
  	"result" -> Derivative[1][u][x]
]
Get[test]