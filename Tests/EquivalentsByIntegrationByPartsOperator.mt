(* Wolfram Language Test file *)
test = "Tests/EquivalentsByIntegrationByPartsOperatorChild.mt"
		Print["   EquivalentsByIntegrationByPartsOperator"];

label = "$Failed"
variables = Association[
	"expression" -> $Failed, 
	"result" -> $Failed
	];
Get[ test ]

label = "Standard example"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"expression" ->  u[x] u''''[x],
	"result" -> {Derivative[2][u][x]^2, -(Derivative[1][u][x]*Derivative[3][u][x]), u[x]*Derivative[4][u][x]}
}];
Get[ test ]

label = "Exponential"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"depth" -> 1,
	"expression" ->  E^u[x] u''[x],
	"result" ->  {-(E^u[x]*Derivative[1][u][x]^2), E^u[x]*Derivative[2][u][x], E^u[x]*u[x]*Derivative[1][u][x]^2 + E^u[x]*u[x]*Derivative[2][u][x]}
}];
Get[ test ]

label = "Exponential: squared derivative"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"depth" -> 1,
	"pars"->{},
	"expression" ->  E^u[x] u[x] Derivative[1][u][x]^2,
	"result" -> {-(E^u[x]*u[x]*Derivative[1][u][x]^2), -(E^u[x]*u[x]^2*Derivative[1][u][x]^2), -(E^u[x]*u[x]^2*Derivative[2][u][x]), 2*E^u[x]*u[x]^2*Derivative[1][u][x]^2 + E^u[x]*u[x]^3*Derivative[1][u][x]^2 + E^u[x]*u[x]^3*Derivative[2][u][x]} 
}];
Get[ test ]

label = "Piecewise" (*THIS TEST IS TAKING TOO MUCH TIME. COMMENTED PARTS OF THE EXPRESSION.*)
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars"->{a},
	(*"depth" -> 10,*)
	"expression" ->  Piecewise[{{u[x]^a u''''[x], a > 0}, {u''''[x], a == 0},{u[x] u''''[x], a == 1},{u[x]^2 u''''[x], a == 2}}, $Failed],
	"result" -> Piecewise[{{$Failed, a < 0}, {{Derivative[4][u][x]}, a == 0}}, {-2*a*u[x]^(-3 + a)*Derivative[1][u][x]^4, a^2*u[x]^(-3 + a)*Derivative[1][u][x]^4, -2*a^3*u[x]^(-3 + a)*Derivative[1][u][x]^4, a^4*u[x]^(-3 + a)*Derivative[1][u][x]^4, -2*a^5*u[x]^(-3 + a)*Derivative[1][u][x]^4, a^6*u[x]^(-3 + a)*Derivative[1][u][x]^4, -2*a^7*u[x]^(-3 + a)*Derivative[1][u][x]^4, a^8*u[x]^(-3 + a)*Derivative[1][u][x]^4, -2*a^9*u[x]^(-3 + a)*Derivative[1][u][x]^4, a^10*u[x]^(-3 + a)*Derivative[1][u][x]^4, -(a*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x]), -2*a^2*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x], -(a^3*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x]), -3*a^4*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x], -(a^5*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x]), -3*a^6*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x], -(a^7*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x]), -3*a^8*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x], -(a^9*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x]), a^10*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x], a*u[x]^(-1 + a)*Derivative[2][u][x]^2, -(a^2*u[x]^(-1 + a)*Derivative[2][u][x]^2), a^3*u[x]^(-1 + a)*Derivative[2][u][x]^2, -(a^4*u[x]^(-1 + a)*Derivative[2][u][x]^2), a^5*u[x]^(-1 + a)*Derivative[2][u][x]^2, -(a^6*u[x]^(-1 + a)*Derivative[2][u][x]^2), a^7*u[x]^(-1 + a)*Derivative[2][u][x]^2, -(a^8*u[x]^(-1 + a)*Derivative[2][u][x]^2), a^9*u[x]^(-1 + a)*Derivative[2][u][x]^2, 3*a^10*u[x]^(-3 + a)*Derivative[1][u][x]^4 - a^11*u[x]^(-3 + a)*Derivative[1][u][x]^4 - 3*a^10*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x], a^10*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x] - a^11*u[x]^(-2 + a)*Derivative[1][u][x]^2*Derivative[2][u][x] - a^10*u[x]^(-1 + a)*Derivative[2][u][x]^2, -(a*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x]), -(a^2*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x]), -(a^3*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x]), -(a^4*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x]), -(a^5*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x]), -(a^6*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x]), -(a^7*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x]), -(a^8*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x]), -(a^9*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x]), -(a^10*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x]), u[x]^a*Derivative[4][u][x], a*u[x]^a*Derivative[4][u][x], -(a^2*u[x]^a*Derivative[4][u][x]), a^3*u[x]^a*Derivative[4][u][x], -(a^4*u[x]^a*Derivative[4][u][x]), a^5*u[x]^a*Derivative[4][u][x], -(a^6*u[x]^a*Derivative[4][u][x]), a^7*u[x]^a*Derivative[4][u][x], -(a^8*u[x]^a*Derivative[4][u][x]), a^9*u[x]^a*Derivative[4][u][x], a^10*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x] - a^11*u[x]^(-1 + a)*Derivative[1][u][x]*Derivative[3][u][x] - a^10*u[x]^a*Derivative[4][u][x]}]
}];
(*Get[ test ]*)

label = "Two variables, two derivatives in x, (balance in x)"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x,y},
	"intVars" -> {x},
	"expression" ->  u[x, y] D[u[x, y], {x, 2}],
	"result" -> {-Derivative[1, 0][u][x, y]^2, u[x, y]*Derivative[2, 0][u][x, y]}
}];
Get[ test ]

label = "Two variables, two derivatives in y, (balance in x)"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x,y},
	"intVars" -> {x},
	"expression" ->  u[x, y] D[u[x, y], {y, 2}],
	"result" -> {-Derivative[0, 1][u][x, y]^2, u[x, y]*Derivative[0, 2][u][x, y]}
	}];
Get[ test ]

label = "Two variables, two derivatives in x"
variables = Association[{
	"depVars" -> {u,v},
	"indVars" -> {x,y},
	"expression" ->  u[x, y] D[v[x, y], {x, 2}],
	"result" -> {-(Derivative[1, 0][u][x, y]*Derivative[1, 0][v][x, y]), v[x, y]*Derivative[2, 0][u][x, y], u[x, y]*Derivative[2, 0][v][x, y]}
	}];
Get[ test ]

label = "Two variables, two derivatives in y"
variables = Association[{
	"depVars" -> {u,v},
	"indVars" -> {x,y},
	"expression" ->  v[x, y] D[u[x, y], {y, 2}],
	"result" -> {-(Derivative[0, 1][u][x, y]*Derivative[0, 1][v][x, y]), v[x, y]*Derivative[0, 2][u][x, y], u[x, y]*Derivative[0, 2][v][x, y]}
	}];
Get[ test ]

label = "Parameters without piecewise result."
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a},
	"depth" -> 0,
	"expression" ->  u[x] u'[x]^a,
	"result" -> Piecewise[{{{u[x]*Derivative[1][u][x]^a, -(u[x]*Derivative[1][u][x]^a) + u[x]^2*Derivative[1][u][x]^(-2 + a)*Derivative[2][u][x] - a*u[x]^2*Derivative[1][u][x]^(-2 + a)*Derivative[2][u][x]}, a != 1}, {{u[x]*Derivative[1][u][x]^a}, a == 1}}, $Failed]
	(*Piecewise[{{{u[x]*Derivative[1][u][x]^a, -(u[x]*Derivative[1][u][x]^a) + u[x]^2*Derivative[1][u][x]^(-2 + a)*Derivative[2][u][x] - a*u[x]^2*Derivative[1][u][x]^(-2 + a)*Derivative[2][u][x]}, -1 + a != 0}, {{u[x]*Derivative[1][u][x]^a}, a == 1}}, $Failed]*)
	}];
Get[ test ]

label = "substitute parameter value"
variables = Association[{
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a},
	"expression" ->  u''''[x] u[x]^a,
	"result" -> {Derivative[2][u][x]^2, -(Derivative[1][u][x]*Derivative[3][u][x]), u[x]*Derivative[4][u][x]}
	}];
Test[
	With[{expression = variables["expression"]},
    	EquivalentsByIntegrationByPartsOperator[variables][expression]/.a->1
	]
    ,
    With[{result = variables["result"]},
    	result
    ]
    ,
    TestID -> "EquivalentsByIntegrationByPartsOperator-20201111-P7BGR8_" <> label
]



   