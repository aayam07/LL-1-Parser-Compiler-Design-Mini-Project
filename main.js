// Function to get an element by its ID
function $element(id) {
    return document.getElementById(id);
  }
  
  // Define EPSILON as a string "Ɛ"
  var EPSILON = "Ɛ";
  
  // Declare variables for the grammar elements
  var alphabet;
  var nonterminals;
  var terminals;
  var rules;
  var firsts;
  var follows;
  var ruleTable;
  var left_prod = [];
  let right_prod = {};
  // Temporary storage for rules after Left Factoring
  let f_prod_no_lf = {};
  
  // Function called when the grammar is changed
  function grammarChanged() {
    // Clear existing table rows
    $element("llTableRows").innerHTML = "";
  
    // Initialize variables
    alphabet = [];
    nonterminals = [];
    terminals = [];
    rules = [];
    firsts = [];
    follows = [];
    ruleTable = [];
    left_prod = [];
    right_prod = {};
    f_prod_no_lf = {};
    rules = $element("grammar").value.split("\n");
  
    // Perform left recursion elimination
    leftRecursion();
    // Display the grammar after left recursion elimination
    $element("left_recursion_grammar").value = rules.join("\n");
  
    // Check if Left Factoring is required
    if (requireLeftFactoring()) {
      // Perform Left Factoring
      removeCommonPrefix();
      // Create a temporary grammar after Left Factoring
      temp_rules = createGrammar();
      rules = temp_rules;
    }
    
    // Display the grammar after Left Factoring
    $element("left_factored_grammar").value = rules.join("\n");
  
    // Collect alphabet, nonterminals, and terminals
    collectAlphabetAndNonterminalsAndTerminals();
    // Collect FIRST sets
    collectFirsts();
    // Collect FOLLOW sets
    collectFollows();
    // Create LL(1) Parsing Table
    makeRuleTable();
  
    // Display the LL(1) Parsing Table
    displayTable();
  
    // Start parsing input
    parseInput();
  }
  
  // Function to handle left recursion in the grammar
  function leftRecursion() {
    temp_rules = [];
    for (i = 0; i < rules.length; i++) {
      recursivePart = [];
      non_recursivePart = [];
      temp1 = rules[i].split("->");
      left_part = temp1[0].trim();
      right_part = temp1.slice(1);
      right_part = right_part[0].split("|");
  
      for (j = 0; j < right_part.length; j++) {
        if (right_part[j].trim().startsWith(left_part.trim())) {
          recursivePart.push(right_part[j].trim());
        } else {
          non_recursivePart.push(right_part[j].trim());
        }
      }
      if (recursivePart.length < 1) {
        for (j = 0; j < right_part.length; j++) {
          temp_rules.push(left_part + "->" + right_part[j].trim());
        }
        continue;
      } else {
        for (k = 0; k < non_recursivePart.length; k++) {
          temp3 = non_recursivePart[k];
          update_left = left_part + "'";
          non_recursivePart[k] = temp3 + " " + update_left;
          temp_rules.push(left_part + "->" + non_recursivePart[k]);
        }
        for (k = 0; k < recursivePart.length; k++) {
          temp3 = recursivePart[k].slice(1);
          update_left = left_part + "'";
          recursivePart[k] = temp3 + " " + update_left;
          temp_rules.push(update_left + "->" + recursivePart[k]);
          if (k + 1 === recursivePart.length) {
            temp_rules.push(update_left + "-> Ɛ");
          }
        }
      }
    }
    rules = temp_rules;
  }
  
  // Function to check if Left Factoring is required
  const requireLeftFactoring = () => {
    for (let i = 0; i < rules.length; i++) {
      let [l, r] = rules[i].split("->");
      left_prod.push(l);
  
      if (!(l in right_prod)) {
        right_prod[l] = r.trim();
      } else {
        right_prod[l] = [].concat(right_prod[l], r.trim());
      }
    }
    const duplicateTerminalSymbol = getDuplicateNonTerminal(left_prod);
    let left_factor = false;
    duplicateTerminalSymbol.map((l) => {
      const common_seq = getCommonCharacters(right_prod[l]);
      if (common_seq.length == 0) {
        left_factor = false;
      } else {
        left_factor = true;
        return;
      }
    });
    return left_factor;
  };
  
 // Function to remove common prefixes in the grammar rules (i.e Perform Left Factoring)
  const removeCommonPrefix = () => {
    const duplicateTerminalSymbol = getDuplicateNonTerminal(left_prod);
    duplicateTerminalSymbol.forEach((l) => {
      const common_seq = getCommonCharacters(right_prod[l]);
  
      if (common_seq.length !== 0) {
        f_prod_no_lf[l] = [`${l} -> ${common_seq.trim()} ${l.trim()}'`];
  
        const uncommon_char = [];
  
        for (const prod of right_prod[l]) {
          [alpha, beta] = prod.split(common_seq);
          uncommon_char.push(beta);
        }
  
        for (const prod of uncommon_char) {
          if (typeof prod !== "undefined" && prod.length !== 0) {
            f_prod_no_lf[l].push(`${l}' -> ${prod}`);
          } else {
            f_prod_no_lf[l].push(`${l}' -> Ɛ`);
          }
        }
      }
    });
  
    //updated rule after performing LF
    f_prod_no_lf = { ...right_prod, ...f_prod_no_lf };
  };
  
  //TODO: Create new function
  
  //Get list of duplicate Terminal symbol
  const getDuplicateNonTerminal = (elements) => {
    return elements.filter((item, index) => elements.indexOf(item) !== index);
  };
  
  //get common characters from the right part of the production
  //incase of multiple rule
  function getCommonCharacters(values) {
    const common_characters = [];
    for (let i = 0; i < values[0].length; i++) {
      let char = values[0].charAt(i);
      let x = 1;
      while (x < values.length) {
        if (values[x].charAt(i) === char) {
          if (x === values.length - 1) {
            common_characters.push(char);
          }
        } else {
          return common_characters.join("");
        }
        x += 1;
      }
    }
  
    return common_characters.join("");
  }
  
  // Function to create grammar rules after Left Factoring
  function createGrammar() {
    const temp_grammar = [];
    for (const [key, value] of Object.entries(f_prod_no_lf)) {
      if (typeof value === "object") {
        value.forEach((v) => {
          if (v.includes("->")) {
            temp_grammar.push(v);
          } else {
            temp_grammar.push(`${key} -> ${v}`);
          }
        });
      } else {
        temp_grammar.push(`${key} -> ${value}`);
      }
    }
    return temp_grammar;
  }
  
  // Function to display the LL(1) Parsing Table
  function displayTable() {
    $element("llTableHead").innerHTML =
      "<th>FIRST</th><th>FOLLOW</th><th>Nonterminal</th>";
  
    for (var i in terminals) {
      $element("llTableHead").innerHTML += "<th>" + terminals[i] + "</th>";
    }
  
    $element("llTableHead").innerHTML += "<th>$</th>";
  
    for (var i in nonterminals) {
      var nonterminal = nonterminals[i];
      var s = "<tr>";
      s += "<tr>";
      s +=
        '<td nowrap="nowrap">{' +
        firsts[nonterminal] +
        '}</td><td nowrap="nowrap">{' +
        follows[nonterminal] +
        '}</td><td nowrap="nowrap">' +
        nonterminal +
        "</td>";
  
      for (var j in terminals) {
        s +=
          '<td nowrap="nowrap">' +
          emptyIfUndefined(ruleTable[nonterminal][terminals[j]]) +
          "</td>";
      }
  
      s +=
        '<td nowrap="nowrap">' +
        emptyIfUndefined(ruleTable[nonterminal]["$"]) +
        "</td>";
  
      s += "</tr>";
  
      $element("llTableRows").innerHTML += s;
    }
  }
  
  // Function to create the LL(1) Parsing Table
  function makeRuleTable() {
    ruleTable = new Object();
  
    for (var i in rules) {
      var rule = rules[i].trim().split("->");
  
      if (rule.length < 2) {
        continue;
      }
  
      var nonterminal = rule[0].trim();
      var development = trimElements(rule[1].trim().split(" "));
  
      var developmentFirsts = collectFirsts3(development);
  
      for (var j in developmentFirsts) {
        var symbol = developmentFirsts[j];
  
        if (symbol != EPSILON) {
          if (ruleTable[nonterminal] == undefined) {
            ruleTable[nonterminal] = new Object();
          }
  
          var oldTableRule = ruleTable[nonterminal][symbol];
  
          if (oldTableRule == undefined) {
            ruleTable[nonterminal][symbol] = rules[i].trim();
          } else {
            ruleTable[nonterminal][symbol] =
              oldTableRule + "<br>" + rules[i].trim();
          }
        } else {
          for (var j in follows[nonterminal]) {
            var symbol2 = follows[nonterminal][j];
  
            if (ruleTable[nonterminal] == undefined) {
              ruleTable[nonterminal] = new Object();
            }
  
            var oldTableRule = ruleTable[nonterminal][symbol2];
  
            if (oldTableRule == undefined) {
              ruleTable[nonterminal][symbol2] = rules[i].trim();
            } else {
              ruleTable[nonterminal][symbol2] =
                oldTableRule + "<br>" + rules[i].trim();
            }
          }
        }
      }
    }
  }
  
  function emptyIfUndefined(string) {
    return string == undefined ? "" : string;
  }
  
  function collectFirsts() {
    firsts = new Object();
  
    var notDone;
  
    do {
      notDone = false;
  
      for (var i in rules) {
        var rule = rules[i].split("->");
  
        if (rule.length < 2) {
          continue;
        }
  
        var nonterminal = rule[0].trim();
        var development = trimElements(rule[1].trim().split(" "));
        var nonterminalFirsts = firsts[nonterminal];
  
        if (nonterminalFirsts == undefined) {
          nonterminalFirsts = [];
        }
  
        if (development.length == 1 && development[0] == EPSILON) {
          notDone |= addUnique(EPSILON, nonterminalFirsts);
        } else {
          notDone |= collectFirsts4(development, nonterminalFirsts);
        }
  
        firsts[nonterminal] = nonterminalFirsts;
      }
    } while (notDone);
  }
  
  /**
   * @param development
   * <br>Array of symbols
   * @param nonterminalFirsts
   * <br>Array of symbols
   * <br>Input-output
   * @return <code>true</code> If <code>nonterminalFirsts</code> has been modified
   */
  function collectFirsts4(development, nonterminalFirsts) {
    var result = false;
    var epsilonInSymbolFirsts = true;
  
    for (var j in development) {
      var symbol = development[j];
      epsilonInSymbolFirsts = false;
  
      if (isElement(symbol, terminals)) {
        result |= addUnique(symbol, nonterminalFirsts);
  
        break;
      }
  
      for (var k in firsts[symbol]) {
        var first = firsts[symbol][k];
  
        epsilonInSymbolFirsts |= first == EPSILON;
        if (first == EPSILON && j + 1 == development.length) {
          result |= addUnique(first, nonterminalFirsts);
        } else if (first !== EPSILON) {
          result |= addUnique(first, nonterminalFirsts);
        }
        // result |= addUnique(first, nonterminalFirsts);
      }
  
      if (!epsilonInSymbolFirsts) {
        break;
      }
    }
  
    if (epsilonInSymbolFirsts) {
      result |= addUnique(EPSILON, nonterminalFirsts);
    }
  
    return result;
  }
  
  /**
   * @param sequence
   * <br>Array of symbols
   */
  function collectFirsts3(sequence) {
    var result = [];
    var epsilonInSymbolFirsts = true;
  
    for (var j in sequence) {
      var symbol = sequence[j];
      epsilonInSymbolFirsts = false;
  
      if (isElement(symbol, terminals)) {
        addUnique(symbol, result);
  
        break;
      }
  
      for (var k in firsts[symbol]) {
        var first = firsts[symbol][k];
  
        epsilonInSymbolFirsts |= first == EPSILON;
        if (first == EPSILON && j + 1 == sequence.length) {
          addUnique(first, result);
        } else if (first !== EPSILON) {
          addUnique(first, result);
        }
        // addUnique(first, result);
      }
  
      epsilonInSymbolFirsts |=
        firsts[symbol] == undefined || firsts[symbol].length == 0;
  
      if (!epsilonInSymbolFirsts) {
        break;
      }
    }
  
    if (epsilonInSymbolFirsts) {
      addUnique(EPSILON, result);
    }
  
    return result;
  }
  
  function collectFollows() {
    follows = new Object();
  
    var notDone;
  
    do {
      notDone = false;
  
      for (var i in rules) {
        var rule = rules[i].split("->");
  
        if (rule.length < 2) {
          continue;
        }
  
        var nonterminal = rule[0].trim();
        var development = trimElements(rule[1].trim().split(" "));
  
        if (i == 0) {
          var nonterminalFollows = follows[nonterminal];
  
          if (nonterminalFollows == undefined) {
            nonterminalFollows = [];
          }
  
          notDone |= addUnique("$", nonterminalFollows);
  
          follows[nonterminal] = nonterminalFollows;
        }
  
        for (var j in development) {
          var symbol = development[j];
  
          if (isElement(symbol, nonterminals)) {
            var symbolFollows = follows[symbol];
  
            if (symbolFollows == undefined) {
              symbolFollows = [];
            }
  
            var afterSymbolFirsts = collectFirsts3(
              development.slice(parseInt(j) + 1)
            );
  
            for (var k in afterSymbolFirsts) {
              var first = afterSymbolFirsts[k];
  
              if (first == EPSILON) {
                var nonterminalFollows = follows[nonterminal];
  
                for (var l in nonterminalFollows) {
                  notDone |= addUnique(nonterminalFollows[l], symbolFollows);
                }
              } else {
                notDone |= addUnique(first, symbolFollows);
              }
            }
  
            follows[symbol] = symbolFollows;
          }
        }
      }
    } while (notDone);
  }
  
  function collectAlphabetAndNonterminalsAndTerminals() {
    for (var i in rules) {
      var rule = rules[i].split("->");
      if (rule.length != 2) {
        continue;
      }
  
      var nonterminal = rule[0].trim();
      var development = trimElements(rule[1].trim().split(" "));
  
      addUnique(nonterminal, alphabet);
      addUnique(nonterminal, nonterminals);
  
      for (var j in development) {
        var symbol = development[j];
  
        if (symbol != EPSILON) {
          addUnique(symbol, alphabet);
        }
      }
    }
  
    subtract(alphabet, nonterminals, terminals);
  }
  
  /**
   * @param result
   * <br>Array
   * <br>Input-output
   * @return <code>result</code>
   */
  function subtract(array1, array2, result) {
    for (var i in array1) {
      var element = array1[i];
  
      if (!isElement(element, array2)) {
        result[result.length] = element;
      }
    }
  
    return result;
  }
  
  /**
   * @return
   * <br>Array
   * <br>New
   */
  function trimElements(array) {
    var result = [];
  
    for (var i in array) {
      result[i] = array[i].trim();
    }
  
    return result;
  }
  
  // Function to check if an element exists in an array
  function isElement(element, array) {
    for (var i in array) {
      if (element == array[i]) {
        return true;
      }
    }
  
    return false;
  }
  
  /**
   * @param array
   * <br>Input-output
   * @return <code>true</code> iff <code>array</code> has been modified
   */
  function addUnique(element, array) {
    if (!isElement(element, array)) {
      array[array.length] = element;
  
      return true;
    }
  
    return false;
  }
  
  function resize(textInput, minimumSize) {
    textInput.size = Math.max(minimumSize, textInput.value.length);
  }
  
  function parseInput() {
    var input = $element("input").value.trim().split(" ");
    var stack = ["$", nonterminals[0]];
    var parsingRows =
      '<tr><td nowrap="nowrap">' +
      stack.join(" ") +
      '</td><td nowrap="nowrap">' +
      input.join(" ") +
      ' $</td nowrap="nowrap"><td></td></tr>\n';
    var maximumStepCount = parseInt($element("maximumStepCount").value);
    var ok = true;
    var tree = new Object();
    tree.label = "root";
    tree.children = [];
    var parents = [tree];
    for (var i = 0, index = 0; i < maximumStepCount && 1 < stack.length; ++i) {
      var stackTop = stack[stack.length - 1];
      var symbol = index < input.length ? input[index] : "$";
  
      if (symbol.trim() == "") {
        symbol = "$";
      }
  
      var rule = "";
      if (stackTop == symbol) {
        stack.pop();
        ++index;
        parents.pop().children.push(symbol);
      } else {
        if (isElement(stackTop, nonterminals)) {
          rule = ruleTable[stackTop][symbol];
          if (rule == undefined) {
            ok = false;
            break;
          }
          if (rule.includes("<br>")) {
            //here
            let temp_rule = rule.split("<br>");
            temp_rule.forEach((r) => {
              if (!r.includes(EPSILON)) {
                rule = r;
              }
            });
            rule = temp_rule[1];
            //to here
            // break;
          }
          var node = new Object();
          node.label = stackTop;
          node.children = [];
          parents.pop().children.push(node);
  
          stack.pop();
  
          var reverseDevelopment = rule
            .split("->")[1]
            .trim()
            .split(" ")
            .slice(0)
            .reverse();
  
          for (var j in reverseDevelopment) {
            parents.push(node);
          }
  
          if (!isElement(EPSILON, reverseDevelopment)) {
            stack = stack.concat(reverseDevelopment);
          } else {
            parents.pop().children.push(EPSILON);
          }
        } else {
          ok = false;
          break;
        }
        if (stack.length == 1 || input.length == 0) {
          ok = true;
        } else {
          ok = false;
        }
      }
  
      parsingRows +=
        '<tr><td nowrap="nowrap">' +
        stack.join(" ") +
        '</td><td nowrap="nowrap">' +
        input.slice(index).join(" ") +
        ' $</td><td nowrap="nowrap">' +
        rule +
        "</td></tr>\n";
    }
  
    $element("parsingTableRows").innerHTML = parsingRows;
  
    $element("input").style.backgroundColor = ok ? "green" : "red";
    $element("input").style.color = "white";
  }
  
  function toString(tree) {
    if (tree.label == undefined) {
      return "" + tree;
    }
  
    var result =
      '<table class="tree" border="1"><thead><tr><th colspan="' +
      tree.children.length +
      '">' +
      tree.label +
      "</th></tr></thead><tbody><tr>";
  
    for (var i in tree.children) {
      result += "<td>" + toString(tree.children[i]) + "</td>";
    }
  
    result += "</tr></tbody></table>";
  
    return result;
  }