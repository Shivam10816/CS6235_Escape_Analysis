package submit_a2;

import java.util.*;

import dont_submit.EscapeQuery;
import javafx.util.Pair;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PrimType;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.*;


// State class for state Stak and Heap Map

class State {
    public Map<String, Set<String>> stack;
    public Map<String, Set<String>> heap;

    public State() {
        this.stack = new HashMap<>();
        this.heap = new HashMap<>();
    }
    
    // Union of state with other
    
    public void union(State other) {
        for (Map.Entry<String, Set<String>> entry : other.stack.entrySet()) {
            String key = entry.getKey();
            Set<String> otherSet = entry.getValue();

            stack.putIfAbsent(key, new HashSet<>());
            stack.get(key).addAll(otherSet);
        }

        for (Map.Entry<String, Set<String>> entry : other.heap.entrySet()) {
            String key = entry.getKey();
            Set<String> otherSet = entry.getValue();

            heap.putIfAbsent(key, new HashSet<>());
            heap.get(key).addAll(otherSet);
        }
    }
    
    // Copy other State
    
    public void copy(State other)  {
        for (Map.Entry<String, Set<String>> entry : other.stack.entrySet()) {
            String key = entry.getKey();
            Set<String> otherSet = entry.getValue();

            this.stack.put(key, new HashSet<>(otherSet));
        }

        for (Map.Entry<String, Set<String>> entry : other.heap.entrySet()) {
            String key = entry.getKey();
            Set<String> otherSet = entry.getValue();
            
            this.heap.put(key, new HashSet<>(otherSet));
        }
    }
    
    // Check If two states are equal
    
    public boolean equals(State other) {
        return this.stack.equals(other.stack) && this.heap.equals(other.heap);
    }
    
    // Check If state is empty
    
    public boolean isEmpty() {
        return stack.isEmpty() && heap.isEmpty();
    }
    
    // Print state content
    
    public void print() {

        System.out.println("Stack:");
        for (Map.Entry<String, Set<String>> entry : stack.entrySet()) {
            System.out.println(entry.getKey() + " -> " + entry.getValue());
        }
        System.out.println("Heap:");
        for (Map.Entry<String, Set<String>> entry : heap.entrySet()) {
            System.out.println(entry.getKey() + " -> " + entry.getValue());
        }
    }
}


public class EscapeAnalysis extends SceneTransformer{
	
	
	// Counter for Objects
	static int counter  =0;         
	
	// Set of all escaped Objects
	
	static Set<String> escapes =  new HashSet<>();
	
	// Map of functions with In and Out summary
	
	static Map<SootMethod,Pair<State,State>> functState = new HashMap<>();
	
	// worklist for interProcess Analysis
	
	static Set<SootMethod> CHAworklist = new HashSet<>();
	static Deque<SootMethod>CHAqueue = new ArrayDeque<>() ;
	
	// Map of New allocaition Nodes that are visited 
	static Map<Unit,String>visited = new HashMap<>();
	
	
	public static void printUnits(UnitGraph unitGraph) {
	    Iterator<Unit> unitIterator = unitGraph.iterator();
	    while (unitIterator.hasNext()) {
	        Unit unit = unitIterator.next();
	        System.out.println("Unit :- "+ unit);
	    }
	}

	
	
	//---------Process Unit-----------------------
	public State processUnit(Unit u , State unitIn) {
		
		
		if(u.toString().contains("java.lang")) {
			return unitIn;
		}
		//System.out.println("Unit :- " + u.toString());
//		System.out.print("--------------------In-----------------\n");
//		unitIn.print();
		
		
		State out ;
		out = new State();
		out.copy(unitIn);
		
		// If Unit is Defination statement
		
		if(u instanceof DefinitionStmt) {
			
			// Get Left and RIght operator
			
			DefinitionStmt st = (DefinitionStmt) u;
			Value Rop = st.getRightOp();
			Value Lop =st.getLeftOp();
			
			
			
			if (Lop.getType() instanceof PrimType || Rop.getType() instanceof PrimType) {
		        // Skip processing the statement, since the left-hand side is a primitive type
		        return unitIn;
		    }
			//-----------X = new A()--------------
			if( Lop instanceof Local && Rop instanceof NewExpr) {
				//System.out.println("New "+u.toString());
				
				
				//--------Make entry in stack according to visited Map -----------
				
				if(!visited.containsKey(u)) {
					
					String Obj = "O"+String.valueOf(counter);
					counter++;
					visited.put(u, Obj);
					Set<String> values =new HashSet<>();
					values.add(Obj);
					out.stack.put(Lop.toString(),values);
						
				}
				else {
					
					Set<String> values =new HashSet<>();
					values.add(visited.get(u));
					out.stack.put(Lop.toString(),values);
				}
				
				//------------Initialize all fields to empty----
				
				// Get the type of the object being created
				
				NewExpr newExpr = (NewExpr) Rop;
				RefType refType = newExpr.getBaseType();
				SootClass sootClass = refType.getSootClass();

				// Get all fields of the class
				
				Chain<SootField> fields =  sootClass.getFields();
				
				String obj =visited.get(u); 
				
				// Initialize each field with empty except static field
				
				for (SootField field : fields) {
					
					if(!field.isStatic()) {
						Set<String> values =new HashSet<>();
						out.heap.put(obj+"."+field.getName(), values);
					} 
				}
				
				 // Check if the class extends Thread
				
				  while (sootClass.hasSuperclass()) {
				    sootClass = sootClass.getSuperclass();
				    if (sootClass.getName().equals("java.lang.Thread")) {
				      // The class extends Thread then object escapes
				      //System.out.println("Class " + sootClass.getName() + " extends Thread");
				      escapes.add(obj);
				      break;
				    }
				  }
			}
			
			//-----------X = Y----------------------
			
			else if( Lop instanceof Local && Rop instanceof Local ) {
				//System.out.println("Copy "+u.toString());
				
				// Update State according to It
				
				Set<String> values = new HashSet<>();
				
				if(unitIn.stack.get(Rop.toString())!=null) {
					values.addAll(unitIn.stack.get(Rop.toString()));
				}
				
				out.stack.put(Lop.toString(), values);
				
				for(String val : values) {
					for(String field : unitIn.heap.keySet()) {
						if(field.contains(val)) {
							out.heap.put(field,unitIn.heap.get(field));
						}
					}
				}
				
			}
			
			//---------------X = Y.f--------------------
			
			else if(Lop instanceof Local && Rop instanceof FieldRef ) {
				//System.out.println("Load "+u.toString());
				
				// If Right operator is INstantField
				
				if (Rop instanceof InstanceFieldRef) {
					InstanceFieldRef fieldRef = (InstanceFieldRef) Rop;
		    	    Value base = fieldRef.getBase();
		    	    SootField field = fieldRef.getField();
		    	    String Rvar = base.toString();
		    	    String fieldName = field.getName();
				    //System.out.println("Variable name: " + Rvar);
				   // System.out.println("Field name: " + fieldName);
				    
				    Set<String> ref = new HashSet<>();
				    Set<String> yref = new HashSet<>();

				    if(unitIn.stack.get(Rvar)!=null) {
				    	yref.addAll(unitIn.stack.get(Rvar));
				    }
				    
				    
				    
				    for(String val : yref) {
				    	
				    	ref.addAll(unitIn.heap.get(val+"."+fieldName));
				    }
				    
				    out.stack.put(Lop.toString(), ref);
					
				}
				
				// // If Right operator is Static Field
				
				else if(Rop instanceof StaticFieldRef) {
					Set<String> ref = new HashSet<>();
					ref.add("Og");
					out.stack.put(Lop.toString(), ref);
				    
				}
			}
			
			//----------------X.f = y--------------------
			
			else if( Lop instanceof FieldRef && Rop instanceof Local) {
				//System.out.println("Store "+u.toString());
				
				// For static Field
				
				if(Lop instanceof StaticFieldRef) {
					
					escapes.addAll(unitIn.stack.get(Rop.toString()));
				}
				
				// For instant Field
				
				else {
					
					// Get variable name and Field Name
					
					InstanceFieldRef fieldRef = (InstanceFieldRef) Lop;
		    	    Value base = fieldRef.getBase();
		    	    SootField field = fieldRef.getField();
		    	    String Lvar = base.toString();
		    	    String fieldName = field.getName();
				   

				    
				    // get values(reference) from stack of Y
		    	    
		    	    Set<String> value = unitIn.stack.get(Rop.toString());
		    	    
		    	    //get set of references from stack of X
		    	    
		    	    Set<String> refs = unitIn.stack.get(Lvar);
		    	    
		    	    //strong update
		    	    
		    	    if(refs.size()<=1) {
		    	    	for(String ref : refs ) {
		    	    		out.heap.put(ref+"."+fieldName, value);
		    	    		if(escapes.contains(ref)) {
		    	    			escapes.addAll(value);
		    	    		}
		    	    	}
		    	    }
		    	    //weak update
		    	    
		    	    else {
		    	    	for(String ref : refs ) {
		    	    		
		    	    		out.heap.get(ref+"."+fieldName).addAll( value);
		    	    		if(escapes.contains(ref)) {
		    	    			escapes.addAll(value);
		    	    		}
		    	    	}
		    	    }
				    
				}
				
			}
		
		}
			
		// -------------------For function Call-------------------------------
		
		else if(u instanceof InvokeStmt) {
			
			if(!u.toString().contains("join") && !u.toString().contains("init") && !u.toString().contains("wait") && !u.toString().contains("notify") && !u.toString().contains("notifyall") ) {
				
				//System.out.println("Method :- "+u.toString());
				String method ;
				
				//---------for start method-------------------
				
				if(u.toString().contains("start")) {
					 method= u.toString().replace("start", "run");
				}
				//----------- For Other Method-----------------
				
				else {
					method =u.toString();
				}
					//System.out.println(method);
					for(SootMethod m : functState.keySet()) {
						
						//if name of methods match
						
						if(method.contains(m.toString())) {
							method = m.toString();   // actual name of function
							Stmt stmt = (Stmt) u;
							VirtualInvokeExpr func = (VirtualInvokeExpr) stmt.getInvokeExpr() ;
							Value baseValue = func.getBase();
							
							//get base name (variable name)
							
							if (baseValue instanceof Local) {
					            Local baseLocal = (Local) baseValue;
					            State newIn = new State();
					            
					            // create newIn state for function
					            
					            newIn.stack.put("this", unitIn.stack.get(baseLocal.toString()));
					             Set<String> values = unitIn.stack.get(baseLocal.toString());
					             
					             for(String val : values) {
					            	 for(String field : unitIn.heap.keySet()) {
					            		 if(field.contains(val)) {
					            			 Set<String> ref = new HashSet<>();
					            			 ref.addAll(unitIn.heap.get(field));
					            			 newIn.heap.put(field,ref);
					            		 }
					            	 }
					             }
					             
					             // If newIn is not equal to oldIn of method
					             
					           
					             if(!newIn.equals(functState.get(m).getKey())) {
					            	 
					            	 // union of new and old
					            	 
					            	 functState.get(m).getKey().union(newIn);
					            	 
					            	 //add to worklist
					            	 
					            	 CHAworklist.add(m);
					            	 CHAqueue.push(m);
					             }
					             
					             
					             State funOut = new State();
					             
					             funOut.copy(functState.get(m).getValue());
					             
					             //---update out as per function out summary--------
					             
					             if(funOut.stack.get("this")!=null) {
					            	 
					            	 Set<String> value = new HashSet<>();
					            	 value.addAll(out.stack.get(baseLocal.toString()));
					            	 for(String val : value) {
					            		 
					            		 for(String field : funOut.heap.keySet()) {
							            	 
						            		 if(field.contains(val)) {
						            			 out.heap.put(field, funOut.heap.get(field));
						            		 }
						 
							             }
					            	 }
					            	 
					             }
					             
					        }
							break;
						}
					}
					//System.out.println(method);	
			}
			
		}
		
//		System.out.print("--------------------out-----------------\n");
//		out.print();
		return out;
	}
	
	public State IntraProcess (Body B, State In) {
		
		
//		System.out.println("------------------IN----------------------");
//		System.out.println("function :- "+B.getMethod().toString());
//		In.print();
//		System.out.println("----------------------------------------");
		
		// Create new Worklist
		
	    Set<Unit> Workset = new HashSet<>();
	    Queue<Unit> worklist = new LinkedList<>();
	    
	    // Create Control flow graph
	    
	    UnitGraph g = new BriefUnitGraph(B);
	   // printUnits(g);
	    Map<Unit,State> unitIn = new HashMap<>();
	    
	    // Initialize all nodes in the CFG with empty state except 1st
	    
	    int count =0;
	    for (Unit u : g.getBody().getUnits()) {
	       State temp = new State();
	       
	       if(count==0) {
	    	   temp.copy(In);
	    	   count++;
	       }
	    	   
	       unitIn.put(u, temp);
	        worklist.offer(u);
	        Workset.add(u);
	    }
	    
	    
	    
	    
	    //--------Perform a BFS traversal of the CFG--------
	    count=0;
	    while (!worklist.isEmpty()) {
	    	
	    	
	    	State effect = new State();
		    State TotalEffect = new State();
		   TotalEffect.copy(In);
		
	        Unit n = worklist.poll();
	        Workset.remove(n);
	        
	        // Get list of predecessors for unit n
	        List<Unit> Pred = g.getPredsOf(n);

	        // Strong Update for single predecessor
	        if(Pred.size()==1){
	        	for(Unit P : Pred) {
	        		
	        		//System.out.println("Unit :- "+ P.toString());
	 	        	effect = processUnit(n,unitIn.get(P));
	 	        	TotalEffect.stack.putAll(effect.stack);
	 	        	TotalEffect.heap.putAll(effect.heap);
	 	        	
	 	        }
	        }
	        
	        // Take union of all predecessor out
	        
	        else {
	        	 for(Unit P : Pred) {
	        		 
	        		 //System.out.println("Unit :- "+ P.toString());
	 	        	effect = processUnit(n,unitIn.get(P));
	 	        	
	 	        	TotalEffect=merge(effect,TotalEffect);
	 	        	
	 	        }
	        }
	        
	        
	        // Add successors of the node to the worklist
	        
	        if(!unitIn.get(n).equals(TotalEffect)) {
	        	
	        	
	        	unitIn.put(n, TotalEffect);
	        	 List<Unit> successors = g.getSuccsOf(n);
	 	        for (Unit succ : successors) {
	 	            	
	 	        		if(Workset.contains(succ)==false) {
	 	        			worklist.offer(succ);
	 	        			Workset.add(succ);
	 	        			
	 	        		}  
	 	        }
	        }
	        
	        

	       
	    }
	    
	    
	    
	    // Get Final Summary of function at return statement
	    
	    State out=new State();

	    for(Unit u :g.getBody().getUnits() ) {
	    	//System.out.println("Unit :- "+ u.toString());
	    	if(g.getSuccsOf(u).size()==0) {
	    		out.copy(unitIn.get(u));
	    		break;
	    	}
	    }

	    
	    
	    
	    
//	    System.out.println("-------------------OUT---------------------");
//		System.out.println("function :- "+B.getMethod().toString());
//		out.print();
//		System.out.println("----------------------------------------"); 
	    
		
	    return out;
		
	}
	
	public static State merge(State s1, State s2) {
		
	    // Create a new state object to hold the merged state
	    State merged = new State();
	    
	    // Merge the stack maps
	    
	    for (String key : s1.stack.keySet()) {
	        if (s2.stack.containsKey(key)) {
	            Set<String> unionSet = new HashSet<String>(s1.stack.get(key));
	            unionSet.addAll(s2.stack.get(key));
	            merged.stack.put(key, unionSet);
	        } else {
	            merged.stack.put(key, s1.stack.get(key));
	        }
	    }
	    for (String key : s2.stack.keySet()) {
	        if (!s1.stack.containsKey(key)) {
	            merged.stack.put(key, s2.stack.get(key));
	        }
	    }
	    
	    // Merge the heap maps
	    
	    for (String key : s1.heap.keySet()) {
	        if (s2.heap.containsKey(key)) {
	            Set<String> unionSet = new HashSet<String>(s1.heap.get(key));
	            unionSet.addAll(s2.heap.get(key));
	            merged.heap.put(key, unionSet);
	        } else {
	            merged.heap.put(key, s1.heap.get(key));
	        }
	    }
	    for (String key : s2.heap.keySet()) {
	        if (!s1.heap.containsKey(key)) {
	            merged.heap.put(key, s2.heap.get(key));
	        }
	    }
	    
	    // Return the merged state object
	    
	    return merged;
	}
	
	// Initialize FunctState IN and Out for each Function
	
	public void init_worklist(CallGraph callGraph) {
		for (Iterator<Edge> edgeIterator = callGraph.iterator(); edgeIterator.hasNext();) {
            Edge edge = edgeIterator.next();

            // Get source and target methods
            
            SootMethod srcMethod = edge.src();
            SootMethod tgtMethod = edge.tgt();

            // Check if the declaring class of the methods is not java.lang.Thread and <init>
            if (!srcMethod.getDeclaringClass().getName().contains("java") &&
                    !tgtMethod.getDeclaringClass().getName().contains("java") &&
                    !srcMethod.getName().equals("<init>") &&
                    !tgtMethod.getName().equals("<init>")) {
                   
                    // Add Methods to function state
            	
            		// Add srcMthod to functState
            	
                    if(functState.containsKey(srcMethod)==false) {
                    	State in = new State();
                        State ret = new State();
                        Pair<State,State> p = new Pair(in, ret);
                    	functState.put(srcMethod,p);
                    }
                    
                    // Add tgtMethod to functState
                    
                    if(functState.containsKey(tgtMethod)==false) {
                    	
                    	State in = new State();
                        State ret = new State();
                        Pair<State,State> p = new Pair(in, ret);
                    	functState.put(tgtMethod,p);
                    
                    }
                    
                }
            }
	}
	
	// Add caller of method M to CHAWORKLIST
	
	public void addCaller(SootMethod m,CallGraph callGraph) {
		for (Iterator<Edge> edgeIterator = callGraph.iterator(); edgeIterator.hasNext();) {
            Edge edge = edgeIterator.next();

            // Get source and target methods
            SootMethod srcMethod = edge.src();
            SootMethod tgtMethod = edge.tgt();

            // Check if the declaring class of the methods is not java.lang.Thread
            if (!srcMethod.getDeclaringClass().getName().contains("java") &&
                    !tgtMethod.getDeclaringClass().getName().contains("java") &&
                    !srcMethod.getName().equals("<init>") &&
                    !tgtMethod.getName().equals("<init>")) {
                    // Print source and target methods
            		if(tgtMethod==m) {
            			CHAqueue.push(srcMethod);
            			CHAworklist.add(srcMethod);
            			
            		}
                    
                   
                  
                }
            }
	}
	
	//-----------InterProcess analysis-----------------
	
	public void InterProcess(CallGraph CHA) {
		
		//--------Initialize FunctionState In and Out summary--------------
		
		init_worklist(CHA);
		
		//---------Add main method to worklist------------
		
		CHAworklist.add(Scene.v().getMainMethod());
		CHAqueue.push(Scene.v().getMainMethod());
		
		//-----------Worklist algorithm------------------
		
		while(!CHAworklist.isEmpty()) {
			SootMethod m = CHAqueue.poll();
			CHAworklist.remove(m);
			//System.out.println(m.getSignature());
			//functState.get(m).getKey().print();
			Body body  = m .getActiveBody();
			
			
			State OUT =new State();
			
			//-----In case of only main function---------
			
			if(functState.get(m)!=null) {
				OUT =IntraProcess(body, functState.get(m).getKey());
			}
			else {
				OUT =IntraProcess(body, new State());
			}
			
			State ret=new State();
			if(!m.getSignature().contains("main")) {
				ret.copy(combineStates(functState.get(m).getKey(), OUT));
			}
			else {
				ret.copy(OUT);
			}

			if(!m.getSignature().contains("main") && ret.equals(functState.get(m).getValue())==false) {
				
				//------------add caller of that function to worklist and queue----------
				State in = functState.get(m).getKey();
				Pair<State,State> p = new Pair<State, State>(in,ret);
				functState.put(m, p);

				addCaller(m, CHA);
				
			}		
		}
	}
	
	//-----Combine variables of in with values of out------
	
	public static State combineStates(State in, State out) {
		
	    State result = new State();
	    for (String key : in.stack.keySet()) {
	        if (out.stack.containsKey(key)) {
	            result.stack.put(key, out.stack.get(key));
	        } else {
	            result.stack.put(key, new HashSet<>());
	        }
	    }
	    for (String key : in.heap.keySet()) {
	        if (out.heap.containsKey(key)) {
	            result.heap.put(key, out.heap.get(key));
	        } else {
	            result.heap.put(key, new HashSet<>());
	        }
	    }
	    return result;
	}
	
	
	//----------Traverse Graph to see edges from function to function----------------
	
	public static void traverseCallGraph(CallGraph callGraph) {
        for (Iterator<Edge> edgeIterator = callGraph.iterator(); edgeIterator.hasNext();) {
            Edge edge = edgeIterator.next();

            // Get source and target methods
            SootMethod srcMethod = edge.src();
            SootMethod tgtMethod = edge.tgt();

            // Check if the declaring class of the methods is not java.lang.Thread
            if (!srcMethod.getDeclaringClass().getName().contains("java") &&
                    !tgtMethod.getDeclaringClass().getName().contains("java") &&
                    !srcMethod.getName().equals("<init>") &&
                    !tgtMethod.getName().equals("<init>")) {
            	
                    // Print source and target methods
                    System.out.println("Source method: " + srcMethod.getSignature());
                    System.out.println("Target method: " + tgtMethod.getSignature());
                    System.out.println("---");
                }
            }
        }
    
	
	public String escape_analysis(Body B , State In) {

//		System.out.println("------------------IN----------------------");
//		System.out.println("function :- "+B.getMethod().toString());
//		In.print();
//		System.out.println("----------------------------------------");
		
		// Create new Worklist
	    Set<Unit> Workset = new HashSet<>();
	    Queue<Unit> worklist = new LinkedList<>();
	    
	    // Create Control flow graph
	    UnitGraph g = new BriefUnitGraph(B);
	    Map<Unit,State> unitIn = new HashMap<>();
	    
	    // Initialize all nodes in the CFG with empty state except 1st
	    
	    int count =0;
	    for (Unit u : g.getBody().getUnits()) {
	       State temp = new State();
	       
	       if(count==0) {
	    	   temp.copy(In);
	    	   count++;
	       }
	    	   
	    
	       unitIn.put(u, temp);
	       

	       //unitIn.get(u).print();
	        worklist.offer(u);
	        Workset.add(u);
	    }
	    
	    
	    
	    
	    //--------Perform a BFS traversal of the CFG--------
	    count=0;
	    while (!worklist.isEmpty()) {
	    	
	    	
	    	State effect = new State();
		    State TotalEffect = new State();
		   TotalEffect.copy(In);
		
	        Unit n = worklist.poll();
	        Workset.remove(n);
	        
	        // Get list of predecessors for unit n
	        List<Unit> Pred = g.getPredsOf(n);

	        
	        if(Pred.size()==1){
	        	for(Unit P : Pred) {

	 	        	effect = processUnit(n,unitIn.get(P));
	 	        	TotalEffect.stack.putAll(effect.stack);
	 	        	TotalEffect.heap.putAll(effect.heap);
	 	        	
	 	        }
	        }
	        
	        //take union of all predecessor out
	        else {
	        	 for(Unit P : Pred) {
	        		// System.out.println(P.toString());
	        		 
	 	        	effect = processUnit(n,unitIn.get(P));
	 	        	
	 	        	TotalEffect=merge(effect,TotalEffect);
	 	        	
	 	        }
	        }
	        
	        
	        // Add successors of the node to the worklist
	        if(!unitIn.get(n).equals(TotalEffect)) {
	        	
	        	
	        	unitIn.put(n, TotalEffect);
	        	 List<Unit> successors = g.getSuccsOf(n);
	 	        for (Unit succ : successors) {
	 	            	
	 	        		if(Workset.contains(succ)==false) {
	 	        			worklist.offer(succ);
	 	        			Workset.add(succ);
	 	        			
	 	        		}  
	 	        }
	        }
	        
	        

	       
	    }
	    
	    State out=new State();

	    
	    
	    for(Unit u :g.getBody().getUnits() ) {
	    	
	    	if(g.getSuccsOf(u).size()==0) {
	    		out.copy(unitIn.get(u));
	    		break;
	    	}
	    }

	    
	    
	    
	    
	    //------Check Map at entermoniter--------------
	   
	    int flag=0;
		for(Unit u : unitIn.keySet()) {
			if(u.toString().contains("entermonitor")) {
//				System.out.println("-----------------------Enter monitor-----------------"); 
				String obj = u.toString().substring(13);
				Set<String> values = unitIn.get(u).stack.get(obj);
				
				for(String val : values) {
					if(escapes.contains(val)) {
						flag=1;              // if Object ecsapes make flag true
						break;
					}
				}
			}
		}
		
		if(flag==0) {
			return "Yes";                  // Synchronization can be removed 
		}
		else {
			return "No";					// Synchronization can`t be removed 
		}
	    
	}
	
	@Override
	protected void internalTransform(String phaseName, Map<String, String> options) {
		/*
		 * Implement your escape analysis here
		 * 
		 */
		
		escapes.add("Og");     // add global object to escape Map
		
		
		
		// Create call graph
		
		CallGraph cg = Scene.v().getCallGraph();
		
		// Print graph
		
		//traverseCallGraph(cg);
		
		// Give Call graph as Input to InterProcess analysis
		
		InterProcess(cg);
		
//		System.out.println("--------------------------------Escape Object-----------------");
//		
//		for(String obj : escapes) {
//			System.out.print(obj+" ");
//		}
		
			// ------Get answers to queries------------
		
			int index=0;
			for(EscapeQuery Q : A2.queryList) {
				
				int functexit =0;
				SootMethod curMethod = null;
				for(SootMethod method : functState.keySet()) {
					
					if(method.toString().contains(Q.getClassName()) && method.toString().contains(Q.getMethodName())) {
						functexit=1;
						curMethod = method;
						break;
					}
				}
				
				//---In method not have any edge in call graph--
				
				if(functexit==0) {
					A2.answers[index]="No";
				}
				
				else {
					A2.answers[index]=escape_analysis(curMethod.getActiveBody(), functState.get(curMethod).getKey());
				}
				
				
				index++;
			}	
	}
	
}
