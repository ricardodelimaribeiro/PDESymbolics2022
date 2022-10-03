(* Wolfram Language Test file *)
	test = "Tests/FindIntegratingFactorBasisOperatorChild.mt";
		Print["   FindIntegratingFactorBasisOperator"];


label = "transport equation"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x, t}
	],
	"operator" -> FindIntegratingFactorBasisOperator,
	"expression"(*problem*) -> Association[
   		"expression" -> {D[u[x, t], t] - D[u[x, t], x]},
   		"monomials" -> Association["degree" -> 1, "derivatives" -> 2]
   	],
   	"result" -> {{1}, {u[x, t]}, {Derivative[0, 2][u][x, t]}, {Derivative[1, 1][u][x, t]}, {Derivative[2, 0][u][x, t]}}
]
Get[test]

label = "kdv"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x, t}
	],
	"operator" -> FindIntegratingFactorBasisOperator,
	"expression"(*problem*) -> Association[
   		"expression" -> {D[u[x, t], t] - u[x, t] D[u[x, t], x] - D[u[x, t], {x, 3}]},
   		"monomials" -> Association["degree" -> 2, "derivatives" -> 2]
   	],
   	"result" -> {{1}, {u[x, t]}, {u[x, t]^2/2 + Derivative[2, 0][u][x, t]}}

]
Get[test]

label = "transport-advection-diffusion system same monomials"
template = Association[
	"variables" -> Association[
		"depVars" -> {u, v}, 
		"indVars" -> {x, t}
	],
	"operator" -> FindIntegratingFactorBasisOperator,
	"expression"(*problem*) -> Association[
   		"expression" -> {D[u[x, t], t] - D[u[x, t], x], D[v[x, t], t] - D[v[x, t], {x, 2}] },
   		"monomials" -> Association["degree" -> 1, "derivatives" -> 2]
   	],
   	"result" -> {{1, 0}, {u[x, t], 0}, {Derivative[0, 1][v][x, t] - Derivative[2, 0][v][x, t], -Derivative[0, 1][u][x, t] + Derivative[1, 0][u][x, t]}, {Derivative[0, 2][u][x, t], 0}, {Derivative[1, 1][u][x, t], 0}, {Derivative[2, 0][u][x, t], 0}, {0, 1}}
]
Get[test]

label = "transport-advection-diffusion system"
template = Association[
	"variables" -> Association[
		"depVars" -> {u, v}, 
		"indVars" -> {x, t}
		],
	"operator" -> FindIntegratingFactorBasisOperator,
	"expression"(*problem*) -> Association[
   		"expression" -> {D[u[x, t], t] - D[u[x, t], x], D[v[x, t], t] - D[v[x, t], {x, 2}] },
   		"monomials" -> {Association["degree" -> 1, "derivatives" -> 2],Association["degree" -> 1, "derivatives" -> 2]}
   		],
   	"result" -> {{1, 0}, {u[x, t], 0}, {Derivative[0, 1][v][x, t] - Derivative[2, 0][v][x, t], -Derivative[0, 1][u][x, t] + Derivative[1, 0][u][x, t]}, {Derivative[0, 2][u][x, t], 0}, {Derivative[1, 1][u][x, t], 0}, {Derivative[2, 0][u][x, t], 0}, {0, 1}}
]
Get[test]

label = "discrete transport"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x, t},
		"VarDOperator" -> DVarDOperator
		],
	"operator" -> FindIntegratingFactorBasisOperator,
	"expression"(*problem*) -> Association[
   		"expression" -> {u[x, t + 1] - u[x, t] - (u[x + 1, t] - u[x, t])},
   		"monomials" -> Association["degree" -> 2, "generators" -> {u[x, t], u[x + 1, t + 1]}]],
   	"result" -> {{1}, {u[x, t] + u[1 + x, 1 + t]}}
]
Get[test]

label = "discrete transport more generators"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"indVars" -> {x, t},
		"VarDOperator" -> DVarDOperator
		],
	"operator" -> FindIntegratingFactorBasisOperator,
	"expression"(*problem*) -> Association[
   		"expression" -> {u[x, t + 1] - u[x, t] - (u[x + 1, t] - u[x, t])},
   		"monomials" -> Association["degree" -> 2, "generators" -> {u[x, t], u[x + 1, t], u[x, t + 1], u[x + 1, t + 1]}]],
   	"result" -> {{1}, {u[x, t] + u[1 + x, 1 + t]}, {u[x, t]^2 + u[x, 1 + t]*u[1 + x, 1 + t] + u[1 + x, t]*u[1 + x, 1 + t]}, {u[x, 1 + t] + u[1 + x, t]}, {u[x, t]*u[x, 1 + t] + u[x, t]*u[1 + x, t] + u[1 + x, 1 + t]^2}, {u[x, 1 + t]^2 + u[x, 1 + t]*u[1 + x, t] + u[1 + x, t]^2}}
]
Get[test]

label = "discrete parametric"
template = Association[
	"variables" -> Association[
		"depVars" -> {u}, 
		"pars" -> {a},
		"indVars" -> {x, t},
		"VarDOperator" -> DVarDOperator
		],
	"operator" -> FindIntegratingFactorBasisOperator,
	"expression"(*problem*) -> Association[
   		"expression" -> {u[x, t + 1] - u[x, t] - a (u[x - 1, t] - u[x + 1, t]) - (1 - a) (u[x - 1, t + 1] - u[x + 1, t + 1])},
   		"monomials" -> Association["degree" -> 2, "generators" -> {u[x, t], u[x + 1, t], u[x - 1, t],  u[x, t + 1], 
  u[x - 1, t + 1], u[x + 1, t + 1]}]],
   	"result" -> Piecewise[{{{{1}}, a == (-1)^(1/3) || a == Root[2 - 15*#1 + 33*#1^2 - 33*#1^3 + 12*#1^4 & , 3, 0] || a == Root[2 - 15*#1 + 33*#1^2 - 33*#1^3 + 12*#1^4 & , 4, 0] || a == Root[1 - 2*#1 - 5*#1^2 + 16*#1^3 - 17*#1^4 + 6*#1^5 & , 4, 0] || a == Root[1 - 2*#1 - 5*#1^2 + 16*#1^3 - 17*#1^4 + 6*#1^5 & , 5, 0] || (-1)^(2/3) + a == 0 || (-I)*Sqrt[3] + 6*a == 3 || I*Sqrt[3] + 6*a == 3 || (-I)*Sqrt[3] + 14*a == 9 || I*Sqrt[3] + 14*a == 9 || a != 1/2}, {{{1}, {u[-1 + x, t] + u[1 + x, 1 + t]}, {u[-1 + x, 1 + t] + u[1 + x, t]}, {u[x, t] + u[x, 1 + t]}}, a == 1/2}}, $Failed]
]
Get[test]