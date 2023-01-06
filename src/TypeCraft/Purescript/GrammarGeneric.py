# creates GrammarGeneric.purs

def createInstance_Generic(name):
  return f'derive instance generic{name} :: Generic {name} _\n'

def createInstance_Show(name):
  return f'instance show{name} :: Show {name} where\n  show x = genericShow x\n'

def createInstance_Eq(name):
  return f'instance eq{name} :: Eq {name} where\n  eq x = genericEq x\n'

def createInstances(name):
  return "\n".join([
    createInstance_Generic(name), 
    createInstance_Eq(name),
    createInstance_Show(name)
  ])

names = [
  "Type",
  "PolyType",
  "TypeArg",
  "Term",
  "TypeBind",
  "TermBind",
  "CtrParam",
  "Constructor",
  "Kind",
  "PolyChange",
  "Change",
  "VarChange",
  "ChangeParam",
  "KindChange",
  "Tooth"
]

def createAllInstances():
  return "\n".join([
    createInstances(name) 
    for name in names
  ])

if __name__ == "__main__":
  # print(createInstances("TypeBind"))
  print(createAllInstances())
