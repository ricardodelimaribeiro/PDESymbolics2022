(* Wolfram Language Test file *)


test = "Tests/LeadingCoefficientOperatorChild.mt";
		Print["   Template"];


label = "unitary"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingCoefficientOperator, 
  	"expression" -> 0,
  	"result" -> 1
]
Get[test]

label = "Length 2"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingCoefficientOperator, 
  	"expression" -> 1,
  	"result" -> 1
]
Get[test]

label = "Length 3"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingCoefficientOperator, 
  	"expression" -> c,
  	"result" -> Piecewise[{{c, c != 0}, {1, c == 0}, {$Failed, True}}]
]
Get[test]

label = "Length 4"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingCoefficientOperator, 
  	"expression" -> a u[x],
  	"result" -> Piecewise[{{a, a != 0}, {1, a == 0}, {$Failed, True}}]
]
Get[test]

label = "Length 5"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingCoefficientOperator, 
  	"expression" -> a u'[x]+b u[x],
  	"result" -> Piecewise[{{a, a != 0}, {b, a == 0 && b != 0}, {1, 
   a == 0 && b == 0}, {$Failed, True}}]
]
Get[test]

label = "Length 6"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> LeadingCoefficientOperator, 
  	"expression" -> Piecewise[{{a u'[x]^2 + c u[x], c != 0}, {u'[x] + 2, 
   c == 0}, {$Failed, True}}],
   
  	"result" -> Piecewise[{{a, c != 0 && a != 0}, {c, c != 0}, {1, c == 0}}, $Failed] 
]
Get[test]