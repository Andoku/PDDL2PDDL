package PDDL2PDDL;

import pddl4j.Parser;
import pddl4j.ErrorManager;
import pddl4j.ErrorManager.Message;
import pddl4j.PDDLObject;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.*;

class Analyzer {
	
public static ArrayList<PDDLObject> parse(String f1, String f2) throws Exception {
    Parser parser = new Parser();
	
	PDDLObject domain = parser.parse(new File(f1));
	PDDLObject problem = parser.parse(new File(f2));
	PDDLObject obj = parser.link(domain, problem);
	
	ErrorManager mgr = parser.getErrorManager();
    if (mgr.contains(Message.ERROR)) {
        mgr.print(Message.ALL);
    } else {
        mgr.print(Message.WARNING);
        System.out.println("\nParsing domain done successfully ...");
        System.out.println("Parsing problem done successfully ...\n");
    }
	
	ArrayList<PDDLObject> a = new ArrayList<PDDLObject>();
	a.add(domain);
	a.add(problem);
	return a;
}

}