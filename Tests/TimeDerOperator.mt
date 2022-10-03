(* Wolfram Language Test file *)
	test = "Tests/TimeDerOperatorChild.mt";
		Print["   TimeDerOperator"];

variables = Association[
	"expression" -> $Failed, 
	"eqRhs"-> {Derivative[2][u][x]},
	"result" -> $Failed
	];

label = "$Failed"
Get[ test ]

variables = Association[
	"expression" -> u[x], 
	"eqRhs"-> {H[u[x],u'[x],u''[x]]},
	"result" -> H[u[x],u'[x],u''[x]],
	"depVars" -> {u},
	"indVars" -> {x}
	];

label = "Identity"
Get[ test ]

variables = Association[
	"depVars" -> {u},
	"indVars" -> {x},
	"eqRhs" -> {u''[x]},
	"expression" -> u[x],
	"result" -> u''[x]
]
label = "Heat equation without Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u},
	"indVars" -> {x},
	"eqRhs" -> {u''[x]},
	"expression" -> u[x],
	"Beautify" -> True,
	"result" -> 0
]
label = "Heat equation with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u},
	"indVars" -> {x},
	"eqRhs" -> {u[x] u'[x] + Derivative[3][u][x]},
	"expression" -> u[x]^2,
	"Beautify" -> False,
	"result" -> 2 u[x] (u[x] u'[x] + Derivative[3][u][x])
]
label = "KdV equation without Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u},
	"indVars" -> {x},
	"eqRhs" -> {u[x] u'[x] + Derivative[3][u][x]},
	"expression" -> u[x]^2,
	"Beautify" -> True,
	"result" -> 0
]
label = "KdV equation with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u,r},
	"indVars" -> {x},
	"eqRhs" -> {H[u'[x]]+ u''[x]-r[x], D[H'[u'[x]]r[x],x]-r''[x]},
	"expression" -> H[u'[x]]r[x],
	"Beautify" -> True,
	"result" -> r[x]*(-(Derivative[1][H][Derivative[1][u][x]]*Derivative[1][r][x]) - Derivative[2][H][Derivative[1][u][x]]*Derivative[2][u][x]^2) 
]
label = "H-J - F-P equation with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {r,u},
	"indVars" -> {x},
	"timederivativeorder" -> 2,
	"eqRhs" -> {D[r[x] u'[x],x],u'[x]^2/2},
	"expression" -> U[r[x]],
	"Beautify" -> True,
	"result" -> r[x]^2 (u'')[x]^2 (U'')[r[x]](*from user-guide-presentation*)
]
label = "Displacement convexity for MFGs with Beautify: Optimal transport";
Get[ test ]

variables = Association[
	"depVars" -> {r,u},
	"indVars" -> {x},
	"timederivativeorder" -> 2,
	"eqRhs" -> {D[r[x] u'[x],x],u'[x]^2/2-g[r[x]]},
	"expression" -> U[r[x]],
	"Beautify" -> True,
	"result" -> ((2*r[x]*Derivative[1][g][r[x]]*Derivative[1][r][x]^2 + 2*r[x]^2*Derivative[2][u][x]^2)*Derivative[2][U][r[x]])/2
]
label = "Displacement convexity for MFGs with Beautify: MFGs";
Get[ test ]

variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x},
	"timederivativeorder" -> 2,
	"eqRhs" -> {v''[x],-u''[x]},
	"expression" -> a[x] (u[x]^2+v[x]^2),
	"Beautify" -> False,
	"result" -> -((4*Derivative[1][a][x]*Derivative[1][u][x] + 2*u[x]*Derivative[2][a][x])*Derivative[2][u][x]) + (-4*Derivative[1][a][x]*Derivative[1][v][x] - 2*v[x]*Derivative[2][a][x])*Derivative[2][v][x]
]
label = "Virial identities for Schrodinger equation: generic a[x] without Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x},
	"timederivativeorder" -> 2,
	"eqRhs" -> {v''[x],-u''[x]},
	"expression" -> a[x] (u[x]^2+v[x]^2),
	"Beautify" -> True,
	"result" -> -2*(2*Derivative[1][a][x]*Derivative[1][u][x]*Derivative[2][u][x] + u[x]*Derivative[2][a][x]*Derivative[2][u][x] + (2*Derivative[1][a][x]*Derivative[1][v][x] + v[x]*Derivative[2][a][x])*Derivative[2][v][x])
]
label = "Virial identities for Schrodinger equation: generic a[x] with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x},
	"timederivativeorder" -> 2,
	"eqRhs" -> {v''[x],-u''[x]},
	"expression" -> x^2 (u[x]^2+v[x]^2),
	"Beautify" -> False,
	"result" -> -((4*u[x] + 8*x*Derivative[1][u][x])*Derivative[2][u][x]) + (-4*v[x] - 8*x*Derivative[1][v][x])*Derivative[2][v][x]
]
label = "Virial identities for Schrodinger equation: x^2 without Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x},
	"timederivativeorder" -> 1,
	"eqRhs" -> {v''[x],-u''[x]},
	"expression" -> (u[x]^2+v[x]^2),
	"Beautify" -> True,
	"result" -> 0
]
label = "Virial identities for Schrodinger equation: 1 with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x},
	"timederivativeorder" -> 2,
	"eqRhs" -> {v''[x],-u''[x]},
	"expression" -> x^2(u[x]^2+v[x]^2),
	"Beautify" -> True,
	"result" -> 4*(2*Derivative[1][u][x]^2 + 2*Derivative[1][v][x]^2)
]
label = "Virial identities for Schrodinger equation: x^2 with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x},
	"timederivativeorder" -> 4,
	"eqRhs" -> {v''[x],-u''[x]},
	"expression" -> x^4 (u[x]^2+v[x]^2),
	"Beautify" -> True,
	"result" -> 576*((2*Derivative[2][u][x]^2)/3 + (2*Derivative[2][v][x]^2)/3)
]
label = "Virial identities for Schrodinger equation: x^4 with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x},
	"timederivativeorder" -> 6,
	"eqRhs" -> {v''[x],-u''[x]},
	"expression" -> x^6 (u[x]^2+v[x]^2),
	"Beautify" -> True,
	"result" -> 69120*((2*Derivative[3][u][x]^2)/3 + (2*Derivative[3][v][x]^2)/3)
]
label = "Virial identities for Schrodinger equation: x^6 with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x},
	"timederivativeorder" -> 8,
	"eqRhs" -> {v''[x],-u''[x]},
	"expression" -> x^8 (u[x]^2+v[x]^2),
	"Beautify" -> True,
	"result" -> 15482880*((2*Derivative[4][u][x]^2)/3 + (2*Derivative[4][v][x]^2)/3)
]
label = "Virial identities for Schrodinger equation: x^8 with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x},
	"timederivativeorder" -> 10,
	"eqRhs" -> {v''[x],-u''[x]},
	"expression" -> x^10 (u[x]^2+v[x]^2),
	"Beautify" -> True,
	"result" -> 5573836800*((2*Derivative[5][u][x]^2)/3 + (2*Derivative[5][v][x]^2)/3)
]
label = "Virial identities for Schrodinger equation: x^10 with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u},
	"indVars" -> {x},
	"timederivativeorder" -> 2,
	"eqRhs" -> {u''[x]},
	"expression" -> u[x]^2,
	"Beautify" -> True,
	"VarDOperator" -> VarDOperator,
	"result" -> 4*Derivative[2][u][x]^2
]
label = "Heat equation, u^2";
Get[ test ]

variables = Association[
	"depVars" -> {u},
	"indVars" -> {n},
	"timederivativeorder" -> 2,
	"eqRhs" -> {u[n+1]-2u[n]+u[n-1]},
	"expression" -> u[n]^2,
	"Beautify" -> True,
	"VarDOperator" -> DVarDOperator,
	"result" -> 4*u[-1 + n]*(6*u[-1 + n] - 8*u[n] + 2*u[1 + n])
]
label = "Discrete heat equation with Beautify";
Get[ test ]

variables = Association[
	"depVars" -> {u},
	"indVars" -> {n},
	"timederivativeorder" -> 2,
	"eqRhs" -> {u[n+1]-2u[n]+u[n-1]},
	"expression" -> u[n]^2,
	"Beautify" -> False,
	"VarDOperator" -> DVarDOperator,
	"result" -> (u[-1 + n] - 2*u[n] + u[1 + n])*(2*u[-1 + n] - 4*u[n] + 2*u[1 + n] + 2*(u[-1 + n] - 2*u[n] + u[1 + n]))
]
label = "Discrete heat equation without Beautify";
Get[ test ]