(* Wolfram Language Test file *)

test = "Tests/PiecewisePolynomialLCMChild.mt";
		Print["   Template"];


label = "unitary"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> PiecewisePolynomialLCM, 
  	"expression" -> Sequence[0,0],
  	"result" -> 0
]
Get[test]


label = "Length2"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> PiecewisePolynomialLCM, 
  	"expression" -> Sequence[u'[x]^2,u[x]],
  	"result" -> u[x] Derivative[1][u][x]^2
]
Get[test]

label = "Length3"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> PiecewisePolynomialLCM, 
  	"expression" -> Sequence[2,u[x]],
  	"result" -> 2 u[x] 
]
Get[test]


label = "Length4"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> PiecewisePolynomialLCM, 
  	"expression" -> Sequence[$Failed,u[x]],
  	"result" -> $Failed 
]
Get[test]

label = "Length5"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> PiecewisePolynomialLCM, 
  	"expression" -> Sequence[u[x],$Failed],
  	"result" -> $Failed 
]
Get[test]


label = "Length6"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u}
  	], 
  	"operator" -> PiecewisePolynomialLCM, 
  	"expression" -> Sequence[{},u[x]],
  	"result" -> {}
]
Get[test]

label = "Length7"
template = Association[
	"variables" -> Association[
		"indVars" -> {x}, 
  		"depVars" -> {u,v}
  	], 
  	"operator" -> PiecewisePolynomialLCM, 
  	"expression" -> Sequence[Piecewise[{{a u'[x]^2 + c u[x], c != 0}, {u'[x] + 2, 
   c == 0}, {$Failed, True}}],v'[x]],
  	"result" -> Piecewise[{{(c u[x] + a Derivative[1][u][x]^2) Derivative[1][v][x], 
   c != 0}, {(2 + Derivative[1][u][x]) Derivative[1][v][x], 
   c == 0}, {$Failed, True}}]
]
Get[test]