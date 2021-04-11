#variant 21
def parseGrammar():
  vt = []
  vn = []

  grammar = dict()

  file = open("v21.txt", "r")
  fileContent = file.read()

  vn = (fileContent[fileContent.index("VN")+4:fileContent.index("\n")-2]).split(", ")
  vt = (fileContent[fileContent.index("VT")+4:fileContent.index("\n", fileContent.index("VT"))-2]).split(", ")

  grammarList = (fileContent[fileContent.index("P")+3:fileContent.index("\n", fileContent.index("P"))-1]).split(", ")

  for grammarRule in grammarList:
    grammarComponents = grammarRule.split(" - ")

    productionResults = list(grammarComponents[1])

    if grammarComponents[0] not in grammar:
      grammar[grammarComponents[0]] = []

    grammar[grammarComponents[0]].append(productionResults)

  from collections import defaultdict
  return defaultdict(lambda: "default", vn=vn, vt=vt, grammar=grammar)

def GetEpsilonDerivationSymbols(grammar):
  epsilonDerivationSymbols = []

  for derivationSymbol in grammar:
    for derivationList in grammar[derivationSymbol]:
      if 'e' in derivationList and len(derivationList) == 1:
        epsilonDerivationSymbols.append(derivationSymbol)
  
  return epsilonDerivationSymbols

def GetIndexOfXSymbolOccurrance(symbolsList, symbol, symbolOccurrenceNumber):
  occurrance = 0;

  for index in range(len(symbolsList)):
    if symbolsList[index] == symbol:
      occurrance += 1
      if occurrance == symbolOccurrenceNumber:
        return index

def GenerateAllPossibleCombinations(analyzedList, symbolToRemove, occurrencesOfEpsilonDerivation):
  from itertools import combinations

  numberCombinations = []
  for x in range(1, occurrencesOfEpsilonDerivation + 1):
    numberCombinations += list(combinations(range(1, occurrencesOfEpsilonDerivation + 1), x))

  allCombinations = []
  for combinationNumber in numberCombinations:
    combination = analyzedList.copy()
    for number in combinationNumber:
      combination.pop(GetIndexOfXSymbolOccurrance(analyzedList, symbolToRemove, number) - len(analyzedList) + len(combination))
    if combination not in allCombinations:
      allCombinations.append(combination)

  return allCombinations

def RemoveEpsilonProductions(grammar):
  while(len(GetEpsilonDerivationSymbols(grammar))):
    epsilonDerivationSymbols = GetEpsilonDerivationSymbols(grammar)

    for epsilonDerivationSymbol in epsilonDerivationSymbols:
      for derivationSymbol in grammar:
        for derivationList in grammar[derivationSymbol]:
          if epsilonDerivationSymbol in derivationList:
            occurrencesOfEpsilonDerivation = derivationList.count(epsilonDerivationSymbol)

            if occurrencesOfEpsilonDerivation == len(derivationList):
              grammar[derivationSymbol].append(['e'])
              continue

            possibleCombinations = GenerateAllPossibleCombinations(derivationList, epsilonDerivationSymbol, occurrencesOfEpsilonDerivation)
            for combination in possibleCombinations:
              if combination not in grammar[derivationSymbol]:
                grammar[derivationSymbol].append(combination)

      #remove epsilon production
      grammar[epsilonDerivationSymbol].remove(['e'])
  return grammar

def RemoveRenaming(grammar, vn):
  for derivationSymbol in grammar:
    for productionList in grammar[derivationSymbol]:
      #condition for finding a renamig
      if len(productionList) == 1 and productionList[0] in vn:
        grammar[derivationSymbol].remove(productionList)
        for production in grammar[productionList[0]]:
          if production not in grammar[derivationSymbol]:
            grammar[derivationSymbol].append(production)
  return grammar

def RemoveInaccessibleSymbols(grammar, vn):
  nonTerminalSymbolsExceptStarting = vn.copy();
  nonTerminalSymbolsExceptStarting.remove("S")

  for nonTerminal in nonTerminalSymbolsExceptStarting:
    isInaccessible = True

    for derivationSymbol in grammar:
      for productionList in grammar[derivationSymbol]:
        if nonTerminal in productionList and derivationSymbol != nonTerminal:
          isInaccessible = False
          break
      if isInaccessible == False:
        break
    
    if isInaccessible:
      grammar.pop(nonTerminal)
  return grammar


def RemoveNonProductiveSymbols(grammar, vn, vt):
  productiveSymbols = []
  isNewProductive = True

  while isNewProductive:
    isNewProductive = False

    for symbol in vn:
      if symbol in grammar:
        productions = grammar[symbol]

        isSymbolProductive = any(all(terminal in vt or terminal in productiveSymbols for terminal in production) for production in productions)
        if isSymbolProductive and symbol not in productiveSymbols:
          isNewProductive = True
          productiveSymbols.append(symbol)
      else:
        productiveSymbols.append(symbol)

  nonProductiveSymbols = [terminal for terminal in vn if terminal not in productiveSymbols]
  
  for nonProductiveSymbol in nonProductiveSymbols:
    for symbol in grammar.copy():
      if symbol in nonProductiveSymbols:
        del grammar[symbol]
        continue
      for production in grammar[symbol]:
        if nonProductiveSymbol in production:
          grammar[symbol].remove(production)
  return grammar

def IsProductionChomskyValid(production, vn, vt):
  return (len(production) == 1 and production[0] in vt) or (len(production) == 2 and production[0] in vn and production[1] in vn)

XCount = 0

def AddMissingProductions(production, grammar, vn, vt):
  global XCount

  if IsProductionChomskyValid(production, vn, vt):
    return production
  
  for index in range(len(production)):
    if IsProductionChomskyValid([production[index]], vn, vt):
      newProduction = production.copy()
      # if such production is already added, just use that one
      addedProductionSymbol = None
      for i in range(1, XCount + 1):
        if [newProduction[index]] in grammar['X' + str(i)]:
          addedProductionSymbol = 'X' + str(i)

      if addedProductionSymbol is not None:
        newProduction[index] = addedProductionSymbol
        
        return AddMissingProductions(newProduction,grammar, vn, vt)
        
      XCount += 1
      newSymbolName = 'X' + str(XCount)
      vn.append(newSymbolName)
      grammar[newSymbolName] = [[newProduction[index]]]
      newProduction[index] = newSymbolName

      return AddMissingProductions(newProduction,grammar, vn, vt)
    
    elif index+1 < len(production) and IsProductionChomskyValid([production[index], production[index + 1]], vn, vt):
      newProduction = production.copy()
      
      # if such production is already added, just use that one
      addedProductionSymbol = None
      for i in range(1, XCount + 1):
        if [newProduction[index], newProduction[index + 1]] in grammar['X' + str(i)]:
          addedProductionSymbol = 'X' + str(i)

      if addedProductionSymbol is not None:
        newProduction[index] = addedProductionSymbol
        del newProduction[index + 1]

        return AddMissingProductions([newProduction[index], newProduction[index+1]],grammar, vn, vt)
        
      XCount += 1
      newSymbolName = 'X' + str(XCount)
      vn.append(newSymbolName)
      grammar[newSymbolName] = [[newProduction[index], newProduction[index + 1]]]
      newProduction[index] = newSymbolName
      del newProduction[index + 1]

      return AddMissingProductions(newProduction,grammar, vn, vt)
      
      
def ChomskyNormalForm(grammar, vn, vt):
  copyGrammar = dict(grammar)

  for symbol in copyGrammar:
    for production in copyGrammar[symbol]:
      if not IsProductionChomskyValid(production, vn, vt):
        indexToReplace = grammar[symbol].index(production)
        grammar[symbol][indexToReplace] = AddMissingProductions(production,grammar, vn, vt)
  return grammar

def printGrammar(grammar, vn, vt):
  print("VN = ", vn)
  print("VT = ", vt)
  print('P = {')

  for symbol in grammar:
    for production in grammar[symbol]:
      print(symbol + " -> " + "".join(production) + ",")

  print("}")
    
parsedGrammar = parseGrammar()
grammarWithoutEpsilonTransations = RemoveEpsilonProductions(parsedGrammar['grammar'])
grammarWithoutRenamings = RemoveRenaming(grammarWithoutEpsilonTransations, parsedGrammar['vn'])
grammarWithoutInaccessibleSymbols = RemoveInaccessibleSymbols(grammarWithoutRenamings, parsedGrammar['vn'])
grammarWithoutNonProductiveSymbols = RemoveNonProductiveSymbols(grammarWithoutInaccessibleSymbols, parsedGrammar['vn'], parsedGrammar['vt'])
grammarChomsky = ChomskyNormalForm(grammarWithoutNonProductiveSymbols, parsedGrammar['vn'], parsedGrammar['vt'])
printGrammar(grammarChomsky, parsedGrammar['vn'], parsedGrammar['vt'])

