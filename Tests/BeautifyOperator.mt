(* Wolfram Language Test file *)
test = "Tests/BeautifyOperatorChild.mt"
		Print["   BeautifyOperator"];

variables = Association[
	"expression" -> $Failed, 
	"result" -> $Failed
	];

label = "$Failed"
Get[ test ]

	variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"intVars" -> {x},
    	"expression" ->  u[x] u''''[x],
    	"result" -> u''[x]^2,
    	"pars"->{},
    	"facts"->True,
    	"generators"->{}
	}];
    label = "Standard example"
    Get[ test ]
    
    	variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"intVars" -> {x},
    	"expression" ->  E^u[x] u''[x],    	
    	"facts"->True,
    	"pars"->{},
    	"generators"->{},
    	"result" -> -E^u[x]u'[x]^2
	}];
    label = "Exponential"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"intVars" -> {x},
    	"indVars" -> {x},
    	"pars" -> {a},
    	"expression" ->  Piecewise[{{u[x]^a u''''[x], a > 0}, {u''''[x], a == 0}}, $Failed],
    	"generators"->{},
    	"result" -> Piecewise[{{$Failed, a < 0}, {(u'')[x]^2, 
  a == 1}, {2 u[x] (u'')[x]^2, 
  a == 2}, {a u[x]^(-2 + a) (u'')[
    x] (-Derivative[1][u][x]^2 + a Derivative[1][u][x]^2 + 
     u[x] (u'')[x]), 0 < a < 1 || 1 < a < 2 || a > 2}},
 0]
	}];
    label = "Piecewise"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"intVars" -> {x},
    	"pars" -> {a},
    	"expression" ->  u[x]^a u''''[x],
    	"generators"->{},
    	"result" -> Piecewise[{{0, a == 0}, {(u'')[x]^2, 
   a == 1}, {2 u[x] (u'')[x]^2, 
   a == 2}, {(-a + a^2) u[x]^(-2 + a) Derivative[1][u][x]^2 (u'')[x] + 
    a u[x]^(-1 + a) (u'')[x]^2, 
   2 a - 3 a^2 + a^3 != 0}}, $Failed]
	}];
    label = "Non Piecewise (did not check the result!!)"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"intVars" -> {x},
    	"generators"->{},
    	"pars" -> {a},
    	"expression" ->  u[x]^a,
    	"result" -> Piecewise[{{0, a == 0}, {u[x]^a, a != 0}}, $Failed]
	}];
    label = "arbitrary power of u[x]"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x,y},
    	"intVars" -> {x},
    	"pars"->{},
    	"facts"->True,
    	"generators"->{},
    	"expression" ->  u[x, y] D[u[x, y], {x, 2}],
    	"result" -> -Derivative[1, 0][u][x, y]^2
	}];
    label = "Two variables, two derivatives in x, (balance in x)"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x,y},
    	"intVars" -> {x},
    	"facts"->True,
    	"pars"->{},
    	"generators"->{},
    	"expression" ->  u[x, y] D[u[x, y], {y, 2}],
    	"result" -> u[x, y]*Derivative[0, 2][u][x, y]
	}];
    label = "Two variables, two derivatives in y, (balance in x)"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x,y},
    	"intVars" -> {x,y},
    	"pars"->{},
    	"facts"->True,
    	"generators"->{},
    	"expression" ->  u[x, y] D[v[x, y], {x, 2}],
    	"result" -> -(Derivative[1, 0][u][x, y]*Derivative[1, 0][v][x, y])
	}];
    label = "Two variables, two derivatives in x"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x,y},
    	"intVars" -> {x,y},
    	"pars"->{},
    	"facts"->True,
    	"generators"->{},
    	"expression" ->  v[x, y] D[u[x, y], {y, 2}],
    	"result" -> -(Derivative[0, 1][u][x, y]*Derivative[0, 1][v][x, y])
	}];
    label = "Two variables, two derivatives in y"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u},
    	"indVars" -> {x},
    	"intVars" -> {x},
    	"pars" -> {a},
    	"generators"->{},
    	"expression" ->  u[x] u''''[x]+u[x] u'[x]^a,
    	"result" -> Piecewise[{{u[x]*Derivative[1][u][x]^a + Derivative[2][u][x]^2, a != 1}, {Derivative[2][u][x]^2, a == 1}}, $Failed]
	}];
    label = "Parameters with piecewise result."
    Get[ test ]
    
   