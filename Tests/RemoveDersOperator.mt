(* Wolfram Language Test file *)
test = "Tests/RemoveDersOperatorChild.mt"
		Print["   RemoveDersOperator"];
	variables = Association[
	"expression" -> $Failed, 
	"result" -> $Failed
	];

label = "$Failed"
Get[ test ]

	
	variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x},
    	"rdVars" -> {u},
    	"expression" ->  v[x] u''''[x],
    	"result" -> u[x]*Derivative[4][v][x]
	}];
    label = "Standard example"
    Get[ test ]
    
    	variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x},
    	"rdVars" -> {u},
    	"expression" ->  E^v[x] u''[x],
    	"result" -> E^v[x]*u[x]*Derivative[1][v][x]^2 + E^v[x]*u[x]*Derivative[2][v][x]
	}];
    label = "Exponential"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x},
    	"rdVars" -> {v},
    	"expression" ->  Piecewise[{{u[x]^a v''''[x], a > 0}, {v''''[x], a == 0}}, $Failed],
    	"result" -> Piecewise[{{$Failed, a < 0}, {a*u[x]^(-4 + a)*v[x]*(-6*Derivative[1][u][x]^4 + 11*a*Derivative[1][u][x]^4 - 6*a^2*Derivative[1][u][x]^4 + a^3*Derivative[1][u][x]^4 + 12*u[x]*Derivative[1][u][x]^2*Derivative[2][u][x] - 18*a*u[x]*Derivative[1][u][x]^2*Derivative[2][u][x] + 6*a^2*u[x]*Derivative[1][u][x]^2*Derivative[2][u][x] - 3*u[x]^2*Derivative[2][u][x]^2 + 3*a*u[x]^2*Derivative[2][u][x]^2 - 4*u[x]^2*Derivative[1][u][x]*Derivative[3][u][x] + 4*a*u[x]^2*Derivative[1][u][x]*Derivative[3][u][x] + u[x]^3*Derivative[4][u][x]), a > 0}}, Derivative[4][v][x]]
	}];
    label = "Piecewise"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x,y},
    	"intVars" -> {x},
    	"rdVars" -> {u},
    	"expression" ->  v[x, y] D[u[x, y], {x, 2}],
    	"result" -> u[x, y]*Derivative[2, 0][v][x, y]
	}];
    label = "Two variables, two derivatives in x, (balance in x)"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x,y},
    	(*"intVars" -> {x},*)
    	"rdVars" -> {u},
    	"expression" ->  v[x, y] D[u[x, y], {y, 2}],
    	"result" -> u[x, y]*Derivative[0, 2][v][x, y]
	}];
    label = "Two variables, two derivatives in y, (balance in x)"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x,y},
    	"rdVars" -> {v},
    	"expression" ->  u[x, y] D[v[x, y], {x, 2}],
    	"result" -> v[x, y]*Derivative[2, 0][u][x, y]
	}];
    label = "Two variables, two derivatives in x"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x,y},
    	"rdVars" -> {v},
    	"expression" ->  v[x, y] D[u[x, y], {y, 2}],
    	"result" -> v[x, y]*Derivative[0, 2][u][x, y]
	}];
    label = "Two variables, two derivatives in y"
    Get[ test ]
    
    variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {x},
    	"pars" -> {a},
    	"rdVars" -> {u},
    	"expression" ->  v[x] u''''[x]+v[x]^a u'[x], (* DG changed this so that the code does not hang - expression must be linear in u *)
    	"result" -> -(a*u[x]*v[x]^(-1 + a)*Derivative[1][v][x]) + u[x]*Derivative[4][v][x]
	}];
    label = "Parameters without piecewise result."
    Get[ test ]
    
   variables = Association[{
		"depVars" -> {u,v},
    	"indVars" -> {t,x,y,z},
    	"pars" -> {a},
    	"rdVars" -> {u},
    	"expression" ->  v[t,x,y,z] (-Derivative[1,0,0,0][u][t,x,y,z] 
    	+ a1[t,x,y,z]Derivative[0,1,0,0][u][t,x,y,z]
    	+ a2[t,x,y,z]Derivative[0,0,1,0][u][t,x,y,z]
    	+ a3[t,x,y,z]Derivative[0,0,0,1][u][t,x,y,z]),
    	"result" -> -(u[t, x, y, z]*v[t, x, y, z]*Derivative[0, 0, 0, 1][a3][t, x, y, z]) - a3[t, x, y, z]*u[t, x, y, z]*Derivative[0, 0, 0, 1][v][t, x, y, z] - u[t, x, y, z]*v[t, x, y, z]*Derivative[0, 0, 1, 0][a2][t, x, y, z] - a2[t, x, y, z]*u[t, x, y, z]*Derivative[0, 0, 1, 0][v][t, x, y, z] - u[t, x, y, z]*v[t, x, y, z]*Derivative[0, 1, 0, 0][a1][t, x, y, z] - a1[t, x, y, z]*u[t, x, y, z]*Derivative[0, 1, 0, 0][v][t, x, y, z] + u[t, x, y, z]*Derivative[1, 0, 0, 0][v][t, x, y, z]
	}];
    label = "Adjoint"
    Get[ test ]
    
   