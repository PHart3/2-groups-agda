**Output of command `agda --profile=internal Final-thms.agda`:**

```
Total                            9,967,489ms              
Miscellaneous                        1,415ms              
Typing                             720,507ms (8,714,445ms)
Typing.CheckRHS                  4,446,376ms              
Typing.OccursCheck               1,590,839ms              
Typing.InstanceSearch            1,308,652ms              
Typing.TypeSig                     643,347ms              
Typing.CheckLHS                      3,848ms     (4,711ms)
Typing.CheckLHS.UnifyIndices           863ms              
Serialization                      347,692ms   (425,574ms)
Serialization.BuildInterface        75,913ms              
Serialization.Compress                 980ms              
Serialization.BinaryEncode             834ms              
Serialization.Sort                     152ms              
DeadCode                               135ms   (318,522ms)
DeadCode.DeadCodeInstantiateFull   302,576ms              
DeadCode.DeadCodeReachable          15,810ms              
Positivity                         304,813ms              
ProjectionLikeness                  67,263ms              
Termination                            114ms    (52,895ms)
Termination.RecCheck                52,766ms              
Termination.Compare                     12ms              
Coverage                            45,454ms    (46,145ms)
Coverage.UnifyIndices                  690ms              
Parsing                                801ms    (18,587ms)
Parsing.OperatorsExpr               17,120ms              
Parsing.OperatorsPattern               665ms              
Scoping                              1,011ms    (12,027ms)
Scoping.InverseScopeLookup          11,016ms              
Deserialization                      3,639ms     (4,704ms)
Deserialization.Compaction           1,064ms              
Highlighting                           789ms              
Import                                 273ms              
Injectivity                             44ms
```
