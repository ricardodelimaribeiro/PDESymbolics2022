(* Wolfram Language Test file *)
test = "Tests/RepresentModNullLagrangiansOperatorChild.mt"
		Print["   RepresentModNullLagrangiansOperator"];

variables = Association[
	"expression" -> $Failed, 
	"result" -> $Failed
	];

label = "$Failed"
Get[ test ]

	variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"pars" -> {a},
    	"expression" ->  8 u[x]^a + 3 u[x]^2,
    	"result" -> Piecewise[{{3*u[x]^2, a == 0}, {11*u[x]^2, a == 2}, {3*u[x]^2 + 8*u[x]^a, -2*a + a^2 != 0}}, $Failed]
    }];
    label = "Piecewise"
    Get[ test ]
    
    
   	variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"expression" -> u'[x]^2 + 7 Derivative[2][u][x]u[x],
    	"result" -> -6 * Derivative[1][u][x]^2
    }];
    label = "Unit term"
    Get[ test ]

   	variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x, y},
    	"expression" -> Derivative[1, 0][u][x, y]^2 - 9 Derivative[2, 0][u][x, y]u[x, y],
    	"result" -> 10 Derivative[1, 0][u][x ,y]^2
    }];
    label = "Unit term more variables"
    Get[ test ]
    
    
    variables = Association[{
        "depVars" -> {u},
        "indVars" -> {x},
        "pars" -> {a},
        "expression" -> u[x]^2 + 9 u[x] u'[x] - 7u'[x]^a + 3 u[x] u''[x] + 7 u[x] u'''[x],
  		"result" -> Piecewise[{{u[x]^2 - 10*Derivative[1][u][x]^2, a == 2}, {u[x]^2 - 7*Derivative[1][u][x]^a + 3*u[x]*Derivative[2][u][x], 2*a - 3*a^2 + a^3 != 0}, {u[x]*(u[x] + 3*Derivative[2][u][x]), a == 0 || a == 1}}, $Failed]
   }];
   label = "works on official notebook"
   Get[ test ]
    
    
   
	variables = Association[{
        "depVars" -> {u},
        "indVars" -> {t},
        "pars" -> {a},
        "expression" -> E^ u[t] u'''[t] + 9 E^ u[t] u''[t] u'[t],
  		"result" -> 8 * E^u[t]*Derivative[1][u][t]*Derivative[2][u][t]
   	}];
   	label = "Exponentials"
   	Get[ test ]
    
	variables = Association[{
        "depVars" -> {u},
        "indVars" -> {x},
        "pars" -> {a},
        "expression" ->  D[u[x, y], x] -
        	v[x, y] Derivative[0, 1][u][x, y] +
        	u[x, y] Derivative[0, 1][v][x, y] ,
  		"result" -> 0
   	}];
   	label = "All Null Lagrangians"
   	Get[ test ]
    
	variables = Association[{
        "depVars" -> {u},
        "indVars" -> {x},
        "pars" -> {a},
        "expression" -> u[x] Derivative[1][u][x] u'''[x]^4 - 2 Derivative[1][u][x]^2 u'''[x]^4,
  		"result" -> (u[x] - 2*Derivative[1][u][x])*Derivative[1][u][x]*Derivative[3][u][x]^4
   	}];
   	label = "No Null Lagrangians"
   	Get[ test ]
    
	variables = Association[{
        "depVars" -> {m},
        "indVars" -> {x},
        "pars" -> {a},
        "expression" -> m'[x] + m[x]^2 + m'[x] * m[x]^2 + 3 m'[x] + 1,
  		"result" -> m[x]^2
   	}];
   	label = "m, not u"
   	Get[ test ]
    
	variables = Association[{
    	"depVars" -> {u},
    	"indVars" -> {x},
    	"pars" -> {a},
    	"expression" -> Piecewise[{{u[x]^a u''''[x], a > 0}, {u''''[x], a == 0}}, $Failed], 
    	"result" -> Piecewise[{{$Failed, a < 0}, {u[x]^a*Derivative[4][u][x], a > 0}}, 0]
    }];
    label = "another piecewise"
    Get[ test ]