(* Wolfram Language Test file *)
test = "Tests/ParametricRefineOperatorChild.mt";
Print["   ParametricRefineOperator"];

label = "$Failed"
variables = Association[
	"expression" -> $Failed, 
	"result" -> $Failed
];

Get[ test ]

label = "a = 0 and a = 2"
variables = Association[
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a},
	"expression" -> u[x]^a + u[x]^2 + a,
	"generators"->{},
	"result" -> Piecewise[{{1 + u[x]^2, a == 0}, {2*(1 + u[x]^2), a == 2}, {a + u[x]^2 + u[x]^a, -2*a + a^2 != 0}}, $Failed]
];
Get[test]
	
label = "two parameters"
variables = Association[
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a,b},
	"expression" -> u[x]^a + u[x]^b + a + b,
	"generators"->{},
	"result" -> 
	Piecewise[{{2, a == 0 && b == 0}, {1 + a + u[x]^a, a != 0 && b == 0}, {2*(b + u[x]^b), a - b == 0 && b != 0}, {1 + b + u[x]^b, a == 0 && b != 0}, {a + b + u[x]^a + u[x]^b, a^2*b - a*b^2 != 0}}, $Failed]
	(*Piecewise[{{2, b == 0 && a == 0}, {1 + b + u[x]^b, a == 0 && b != 0}, {1 + a + u[x]^a, b == 0 && a != 0}, {2*(b + u[x]^b), a - b == 0 && b != 0}, {a + b + u[x]^a + u[x]^b, a^2*b - a*b^2 != 0}}, $Failed]*)
	(*Piecewise[{{2, b == 0 && a == 0}, {1 + b + u[x]^b, a == 0 && b != 0}, {1 + a + u[x]^a, b == 0 && a != 0}, {2*(a + u[x]^a), a - b == 0 && b != 0}, {a + b + u[x]^a + u[x]^b, a^2*b - a*b^2 != 0}}, $Failed]*) (*see a=b case*)
];
Get[test]
	
label = "system of two dependent variables of two independent ones"
variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x,y},
	"pars" -> {a,b},
	"expression" -> {u[x,y]^a + u[x,y]^b, D[u[x,y]^a v[x, y], x] - D[u[x, y]^2 v[x, y]^b, x]},
	"result" -> 
	Piecewise[{{{2, -2*u[x, y]*Derivative[1, 0][u][x, y] + Derivative[1, 0][v][x, y]}, a == 0 && b == 0}, {{2*u[x, y]^a, a*u[x, y]^(-1 + a)*v[x, y]*Derivative[1, 0][u][x, y] - 2*u[x, y]*v[x, y]^a*Derivative[1, 0][u][x, y] + u[x, y]^a*Derivative[1, 0][v][x, y] - a*u[x, y]^2*v[x, y]^(-1 + a)*Derivative[1, 0][v][x, y]}, (a - b == 0 && -2*b + b^2 != 0) || (a - b == 0 && -b + b^2 != 0) || (a - b == 0 && 2*b - 3*b^2 + b^3 != 0)}, {{u[x, y]*(1 + u[x, y]), 0}, a == 2 && b == 1}, {{1 + u[x, y]^a, -2*u[x, y]*Derivative[1, 0][u][x, y] + a*u[x, y]^(-1 + a)*v[x, y]*Derivative[1, 0][u][x, y] + u[x, y]^a*Derivative[1, 0][v][x, y]}, b == 0 && a != 0}, {{1 + u[x, y]^b, -2*u[x, y]*v[x, y]^b*Derivative[1, 0][u][x, y] + Derivative[1, 0][v][x, y] - b*u[x, y]^2*v[x, y]^(-1 + b)*Derivative[1, 0][v][x, y]}, a == 0 && b != 0}, {{u[x, y]^a + u[x, y]^b, a*u[x, y]^(-1 + a)*v[x, y]*Derivative[1, 0][u][x, y] - 2*u[x, y]*v[x, y]^b*Derivative[1, 0][u][x, y] + u[x, y]^a*Derivative[1, 0][v][x, y] - b*u[x, y]^2*v[x, y]^(-1 + b)*Derivative[1, 0][v][x, y]}, (a != 2 && -2*a^2*b + a^3*b + 2*a*b^2 - a^2*b^2 != 0) || (a != 2 && -(a^2*b) + a*b^2 + a^2*b^2 - a*b^3 != 0) || (-2*a^2*b + a^3*b + 2*a*b^2 - a^2*b^2 != 0 && b != 1) || (-(a^2*b) + a*b^2 + a^2*b^2 - a*b^3 != 0 && b != 1)}}, $Failed]
	(*Piecewise[{{{2, -2*u[x, y]*Derivative[1, 0][u][x, y] + Derivative[1, 0][v][x, y]}, b == 0 && a == 0}, {{2*u[x, y]^b, b*u[x, y]^(-1 + b)*v[x, y]*Derivative[1, 0][u][x, y] - 2*u[x, y]*v[x, y]^b*Derivative[1, 0][u][x, y] + u[x, y]^b*Derivative[1, 0][v][x, y] - b*u[x, y]^2*v[x, y]^(-1 + b)*Derivative[1, 0][v][x, y]}, (a - b == 0 && -2*b + b^2 != 0) || (a - b == 0 && -b + b^2 != 0) || (a - b == 0 && 2*b - 3*b^2 + b^3 != 0)}, {{1 + u[x, y]^b, -2*u[x, y]*v[x, y]^b*Derivative[1, 0][u][x, y] + Derivative[1, 0][v][x, y] - b*u[x, y]^2*v[x, y]^(-1 + b)*Derivative[1, 0][v][x, y]}, a == 0 && b != 0}, {{1 + u[x, y]^a, -2*u[x, y]*Derivative[1, 0][u][x, y] + a*u[x, y]^(-1 + a)*v[x, y]*Derivative[1, 0][u][x, y] + u[x, y]^a*Derivative[1, 0][v][x, y]}, b == 0 && a != 0}, {{u[x, y]*(1 + u[x, y]), 0}, b == 1 && a == 2}, {{u[x, y]^a + u[x, y]^b, a*u[x, y]^(-1 + a)*v[x, y]*Derivative[1, 0][u][x, y] - 2*u[x, y]*v[x, y]^b*Derivative[1, 0][u][x, y] + u[x, y]^a*Derivative[1, 0][v][x, y] - b*u[x, y]^2*v[x, y]^(-1 + b)*Derivative[1, 0][v][x, y]}, -2*a^2*b + a^3*b + 2*a*b^2 - a^2*b^2 != 0 || -(a^2*b) + a*b^2 + a^2*b^2 - a*b^3 != 0}}, $Failed]*)
	(*Piecewise[{{{2, -2*u[x, y]*Derivative[1, 0][u][x, y] + Derivative[1, 0][v][x, y]}, b == 0 && a == 0}, {{2*u[x, y]^a, a*u[x, y]^(-1 + a)*v[x, y]*Derivative[1, 0][u][x, y] - 2*u[x, y]*v[x, y]^a*Derivative[1, 0][u][x, y] + u[x, y]^a*Derivative[1, 0][v][x, y] - a*u[x, y]^2*v[x, y]^(-1 + a)*Derivative[1, 0][v][x, y]}, (a - b == 0 && -2*b + b^2 != 0) || (a - b == 0 && -b + b^2 != 0) || (a - b == 0 && 2*b - 3*b^2 + b^3 != 0)}, {{1 + u[x, y]^b, -2*u[x, y]*v[x, y]^b*Derivative[1, 0][u][x, y] + Derivative[1, 0][v][x, y] - b*u[x, y]^2*v[x, y]^(-1 + b)*Derivative[1, 0][v][x, y]}, a == 0 && b != 0}, {{1 + u[x, y]^a, -2*u[x, y]*Derivative[1, 0][u][x, y] + a*u[x, y]^(-1 + a)*v[x, y]*Derivative[1, 0][u][x, y] + u[x, y]^a*Derivative[1, 0][v][x, y]}, b == 0 && a != 0}, {{u[x, y]*(1 + u[x, y]), 0}, b == 1 && a == 2}, {{u[x, y]^a + u[x, y]^b, a*u[x, y]^(-1 + a)*v[x, y]*Derivative[1, 0][u][x, y] - 2*u[x, y]*v[x, y]^b*Derivative[1, 0][u][x, y] + u[x, y]^a*Derivative[1, 0][v][x, y] - b*u[x, y]^2*v[x, y]^(-1 + b)*Derivative[1, 0][v][x, y]}, -2*a^2*b + a^3*b + 2*a*b^2 - a^2*b^2 != 0 || -(a^2*b) + a*b^2 + a^2*b^2 - a*b^3 != 0}}, $Failed]*) (*see a=b case*)
];
(*Get[test]*)
(*TODO what is wrong with this test?*)	
label = "empty"
variables = Association[
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a},
	"expression" -> {},
	"result" -> {}
];
Get[test]
	
label = "from ugp 1"
variables = Association[
	"depVars" -> {u,v},
	"indVars" -> {x},
	"pars" -> {a,b},
	"expression" -> {u[x] + u[x]^a, u[x]^2 + 7 u[x]^(2 - a),  1},
	"generators"->{},
	"result" -> Piecewise[{{{2*u[x], u[x]^(2 - a)*(7 + u[x]^a), 1}, a == 1}, 
  {{u[x] + u[x]^a, 8*u[x]^2, 1}, a == 0}, 
  {{u[x] + u[x]^a, u[x]^(2 - a)*(7 + u[x]^a), 1}, a != 0 && a != 1}}, $Failed]
];
Get[test]

label = "from ugp 2"
variables = Association[
	"depVars" -> {u},
	"indVars" -> {x},
	"pars" -> {a,b},
	"expression" -> u'[x]^2 +  u'[x]^a + u'[x]^(b - a),
	"refine"-> True,
	"generators"->{},
	"result" -> 
	Piecewise[{{3*Derivative[1][u][x]^2, 
   a == 2 && b == 4}, {2*Derivative[1][u][x]^2 + 
    Derivative[1][u][x]^a, 
   2 + a == b && b != 4}, {Derivative[1][u][x]^2 + 
    2*Derivative[1][u][x]^a, 
   2*a == b && 2 + a != b && b != 4}, {2*Derivative[1][u][x]^2 + 
    Derivative[1][u][x]^(-2 + b), 
   a == 2 && 2*a != b && 2 + a != b && 
    b != 4}, {Derivative[1][u][x]^2 + Derivative[1][u][x]^a + 
    Derivative[1][u][x]^(-a + b), (a != 2 && 2*a != b && 
      2 + a != b && (-2 + a)*(2 + a - b)*(2*a - b) != 0) || (a != 
       2 && (-2 + a)*(2 + a - b)*(2*a - b) != 0 && b == 4)}}, $Failed]
	(*Piecewise[{{3*Derivative[1][u][x]^2, a == 2 && b == 4}, {2*Derivative[1][u][x]^2 + Derivative[1][u][x]^a, a - b == -2 && b != 4}, {Derivative[1][u][x]^2 + 2*Derivative[1][u][x]^a, 2*a - b == 0 && b != 4}, {2*Derivative[1][u][x]^2 + Derivative[1][u][x]^(-2 + b), a == 2 && b != 4}, {Derivative[1][u][x]^2 + Derivative[1][u][x]^a + Derivative[1][u][x]^(-a + b), (a != 2 && b == 4) || -8*a + 2*a^3 + 4*b + 4*a*b - 3*a^2*b - 2*b^2 + a*b^2 != 0}}, $Failed]*)
	(*Piecewise[{{3*Derivative[1][u][x]^2, b == 4 && a == 2}, {2*Derivative[1][u][x]^2 + Derivative[1][u][x]^(-2 + b), a == 2 && b != 4}, {2*Derivative[1][u][x]^2 + Derivative[1][u][x]^a, a - b == -2 && b != 4}, {Derivative[1][u][x]^2 + 2*Derivative[1][u][x]^a, 2*a - b == 0 && b != 4}, {Derivative[1][u][x]^2 + Derivative[1][u][x]^a + Derivative[1][u][x]^(-a + b), -8*a + 2*a^3 + 4*b + 4*a*b - 3*a^2*b - 2*b^2 + a*b^2 != 0}}, $Failed]*)
];
Get[test]
	
label = "from ugp 3"
variables = Association[
	"depVars" -> {u},
	"genFuns" -> {V},
	"indVars" -> {x},
	"pars" -> {a},
	"expression" -> V'[u[x]] u'[x] - V'[u[x]] u'[x]^a,
	"refine"-> True,
	"generators"->{},
	"result" -> Piecewise[{{0, a == 1}, {-((-Derivative[1][u][x] + Derivative[1][u][x]^a)*Derivative[1][V][u[x]]), a != 1}}, $Failed]
];
Get[test]



(*TODO take tests from user guide for parametricrefine*)