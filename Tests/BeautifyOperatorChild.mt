(* Wolfram Language Test file *)

Test[
    With[ {expression = variables["expression"],result = variables["result"]},
        With[ {computation = BeautifyOperator[Append["VarDOperator"->VarDOperator]@variables][expression]},
            Which[
                result===computation,
                True, 
                PiecewiseEqualOperator[variables][result, computation] === True,
                True,
                True,
                Print["Expected output:\n",result, "Actual output\n",computation];
                {computation, variables}
            ]
        ]
    ]
    ,
    True
    ,
    TestID -> "BeautifyOperator-20220927-M7B7R8_" <> label
]

