**Output of command `agda --profile=internal Final-thms.agda`:**

```
Total                            10,048,210ms              
Miscellaneous                         1,378ms              
Typing                              698,850ms (8,747,264ms)
Typing.CheckRHS                   4,470,669ms              
Typing.OccursCheck                1,608,198ms              
Typing.InstanceSearch             1,320,723ms              
Typing.TypeSig                      644,154ms              
Typing.CheckLHS                       3,775ms     (4,657ms)
Typing.CheckLHS.UnifyIndices            882ms              
Serialization                       374,807ms   (461,301ms)
Serialization.BuildInterface         84,506ms              
Serialization.Compress                  982ms              
Serialization.BinaryEncode              801ms              
Serialization.Sort                      203ms              
Positivity                          310,633ms              
DeadCode                                142ms   (305,930ms)
DeadCode.DeadCodeInstantiateFull    290,656ms              
DeadCode.DeadCodeReachable           15,131ms              
ProjectionLikeness                   74,823ms              
Coverage                             55,453ms    (56,137ms)
Coverage.UnifyIndices                   683ms              
Termination                             117ms    (54,581ms)
Termination.RecCheck                 54,448ms              
Termination.Compare                      11ms              
Parsing                                 750ms    (18,512ms)
Parsing.OperatorsExpr                17,094ms              
Parsing.OperatorsPattern                666ms              
Scoping                                 992ms    (11,997ms)
Scoping.InverseScopeLookup           11,005ms              
Deserialization                       3,640ms     (4,649ms)
Deserialization.Compaction            1,009ms              
Highlighting                            714ms              
Import                                  254ms              
Injectivity                              43ms
```
