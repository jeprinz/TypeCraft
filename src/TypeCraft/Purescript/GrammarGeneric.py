# creates GrammarGeneric.purs

def createInstance_Generic(name):
  return f"derive instance generic{name} :: Generic {name} _"

def createInstance_EncodeJson(name):
  return f"instance encode{name} :: EncodeJson {name} where encodeJson x = genericEncodeJson x"

def createInstance_DecodeJson(name):
  return f"instance decode{name} :: DecodeJson {name} where decodeJson x = genericDecodeJson x"

def createInstance_Show(name):
  return f"instance show{name} :: Show {name} where show x = genericShow x"

def createInstance_Eq(name):
  return f"instance eq{name} :: Eq {name} where eq x = genericEq x"

def createInstances(name):
  return "\n".join([
    createInstance_Generic(name), 
    createInstance_EncodeJson(name),
    createInstance_DecodeJson(name),
    createInstance_Eq(name),
    createInstance_Show(name),
    ""
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
  "Tooth",
  "TypeVar",
  "SubChange",
  "CTypeVar"
]

def createAllInstances():
  return "\n".join([
    createInstances(name) 
    for name in names
  ])

if __name__ == "__main__":
  # print(createInstances("TypeBind"))
  print(createAllInstances())
