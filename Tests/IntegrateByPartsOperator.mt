(* Wolfram Language Test file *)
test = "Tests/IntegrateByPartsOperatorChild.mt"
		Print["   IntegrateByPartsOperator"];

variables = Association[
	"expression" -> $Failed, 
	"result" -> $Failed
	];

label = "$Failed"
Get[ test ]

	variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"expression" ->  u[x] u''''[x],
    	"result" -> u''[x]^2
	}];
    label = "Standard example"
    Get[ test ]
    
    	variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"expression" ->  E^u[x] u''[x],
    	"result" -> -E^u[x]u'[x]^2
	}];
    label = "Exponential"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"expression" ->  Piecewise[{{u[x]^a u''''[x], a > 0}, {u''''[x], a == 0}}, $Failed],
    	"result" -> Piecewise[{{$Failed, a < 0}, {a*u[x]^(-2 + a)*Derivative[2][u][x]*(-Derivative[1][u][x]^2 + a*Derivative[1][u][x]^2 + u[x]*Derivative[2][u][x]), a > 0}}, 0]
	}];
    label = "Piecewise"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x,y},
    	"intVars" -> {x},
    	"expression" ->  u[x, y] D[u[x, y], {x, 2}],
    	"result" -> -Derivative[1, 0][u][x, y]^2
	}];
    label = "Two variables, two derivatives in x, (balance in x)"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x,y},
    	"intVars" -> {x},
    	"expression" ->  u[x, y] D[u[x, y], {y, 2}],
    	"result" -> u[x, y]*Derivative[0, 2][u][x, y]
	}];
    label = "Two variables, two derivatives in y, (balance in x)"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x,y},
    	"expression" ->  u[x, y] D[v[x, y], {x, 2}],
    	"result" -> -(Derivative[1, 0][u][x, y]*Derivative[1, 0][v][x, y])
	}];
    label = "Two variables, two derivatives in x"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x,y},
    	"expression" ->  v[x, y] D[u[x, y], {y, 2}],
    	"result" -> -(Derivative[0, 1][u][x, y]*Derivative[0, 1][v][x, y])
	}];
    label = "Two variables, two derivatives in y"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"pars" -> {a},
    	"expression" ->  u[x] u''''[x]+u[x] u'[x]^a,
    	"result" -> u[x]*Derivative[1][u][x]^a + Derivative[2][u][x]^2
	}];
    label = "Parameters without piecewise result."
    Get[ test ]
    
   