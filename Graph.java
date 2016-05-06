import java.util.*;

public class Graph {

  // RECEIVER vertex (node) edges represent all the wants on an item's list.
  // SENDER vertex (node) edges represent all the items wanting this item.
  // In other words, the edges are items this item is willing to receive (for
  // RECEIVER) or to whom the item might be sent (for SENDER).
  static enum VertexType { RECEIVER, SENDER }

  public static class Vertex {
    String name;
    String user;
    boolean isDummy;
    VertexType type;

    Vertex(String name, String user, boolean isDummy, VertexType type) {
      this.name = name;
      this.user = user;
      this.isDummy = isDummy;
      this.type = type;
    }

    // A list of edges (connections) between this vertex (node) and others
    List<Edge> edges = new ArrayList<Edge>();
    // This array will be a copy of the finished list from above
    // We use arrays because they're probably easier/faster than lists during computation
    Edge[] EDGES;

    // Internal data for graph algorithms
    private long minimumInCost = Long.MAX_VALUE; // only kept in the senders
    Vertex twin;
    private int mark = 0; // flag used for marking as visited in dfs and dijkstra
    Vertex match = null; // the vertex to which this vertex is currently matched
    long matchCost = 0;
    private Vertex from = null; // the node associated with the cheapest path in dijkstra
    private long price = 0;
    private Heap.Entry heapEntry = null; // contains the current cost (see "from" vertex)
    private int component = 0; // used for removing impossible edges
    boolean used = false; // Note: this variable is (ironically) not used

    Vertex savedMatch = null;
    long savedMatchCost = 0;
  }

  public static class Edge {
    Vertex receiver;
    Vertex sender;
    long cost;

    Edge(Vertex receiver,Vertex sender,long cost) {
      // Test parameter validity
      assert receiver.type == VertexType.RECEIVER;
      assert sender.type == VertexType.SENDER;

      // Set local variables
      this.receiver = receiver;
      this.sender = sender;
      this.cost = cost;
    }

    private Edge() {} // hide default constructor
  }

  public Vertex getVertex(String name) {
    return nameMap.get(name); // returns null if name is undefined
  }

  public Vertex addVertex(String name,String user,boolean isDummy) {
    assert !frozen; // nothing should be added to a graph once it is frozen
    assert getVertex(name) == null; // make sure this name is unique
    Vertex receiver = new Vertex(name,user,isDummy,VertexType.RECEIVER);
    receivers.add(receiver);
    nameMap.put(name,receiver); // add this to the list of used names

    Vertex sender = new Vertex(name+" sender",user,isDummy,VertexType.SENDER);
    senders.add(sender);
    receiver.twin = sender;
    sender.twin = receiver;

    return receiver;
  }

  public Edge addEdge(Vertex receiver,Vertex sender,long cost) {
    assert !frozen; // nothing should be added to a graph once it is frozen

    // Create an edge (a connection) and add it to both vertices (nodes)
    Edge edge = new Edge(receiver,sender,cost);
    receiver.edges.add(edge);
    sender.edges.add(edge);
    // Check if the sending vertex (node) now has a lower minimum cost
    // Note: this will be recalculated anew after removing edges
    sender.minimumInCost = Math.min(cost,sender.minimumInCost);
    return edge;
  }

  public Edge getEdge(Vertex receiver,Vertex sender) {
    for (Edge edge : receiver.edges) {
      if (edge.sender == sender) return edge;
    }
    return null;
  }

  boolean frozen = false; // the graph is unfrozen and ready for additions by default

  // The graph can be "frozen" from adding new elements. When we do this,
  // we convert the lists (great for checking/adding things) to arrays
  // (better for iterating and speed).
  void freeze() {
    assert !frozen; // make sure we're not freezing it twice

    // Convert receivers and senders to arrays for easier handling
    RECEIVERS = receivers.toArray(new Vertex[0]);
    SENDERS = senders.toArray(new Vertex[0]);
    // Convert edges to an array for easier handling
    Edge[] tmp = new Edge[0];
    for (Vertex v : RECEIVERS) v.EDGES = v.edges.toArray(tmp);
    for (Vertex v : SENDERS) v.EDGES = v.edges.toArray(tmp);

    frozen = true; // mark the graph as frozen; no more adding may occur
  }

  // Track the receiver and sender vertices (nodes) while we are populating them
  List<Vertex> receivers = new ArrayList<Vertex>();
  List<Vertex> senders   = new ArrayList<Vertex>();
  // These arrays will be copies of the finished lists from above
  // We use arrays because they're probably easier/faster than lists during computation
  Vertex[] RECEIVERS;
  Vertex[] SENDERS;

  // Keep track of orphaned items that were not connected to other items after
  // culling unusable edges
  List<Vertex> orphans = new ArrayList<Vertex>();

  // The nameMap helps make sure we don't duplicate vertex names
  // and lets us find vertices (nodes) by their names
  private HashMap<String,Vertex> nameMap = new HashMap<String,Vertex>();

  // Note: This function is not called
  void print() {
    assert frozen; // the graph should only be printed when we are done adding things
    for (Vertex v : RECEIVERS) {
      System.out.print(v.name + " :");
      for (Edge e : v.EDGES) {
        if (e.sender != e.receiver.twin)
          System.out.print(" " + e.sender.name);
      }
      System.out.println();
    }
  }

  private int timestamp = 0;
  private void advanceTimestamp() { timestamp++; }
  private int component = 0; // used in determining impossible edges

  // Keep track of which sender vertices have had their receiver twin visited
  private List<Vertex> finished;

  void visitReceivers(Vertex receiver) {
    assert receiver.type == VertexType.RECEIVER;
    // Mark this receiver as visited
    receiver.mark = timestamp;
    // Visit all the receivers of this receiver
    for (Edge edge : receiver.EDGES) {
      Vertex v = edge.sender.twin;
      if (v.mark != timestamp) visitReceivers(v);
    }
    // Add the twin sender vertex (node) to the queue for visitSenders()
    finished.add(receiver.twin);
  }
  void visitSenders(Vertex sender) {
    assert sender.type == VertexType.SENDER;
    sender.mark = timestamp; // mark this sender as visited
    // Visit all the senders of this sender
    for (Edge edge : sender.EDGES) {
      Vertex v = edge.receiver.twin;
      if (v.mark != timestamp) visitSenders(v);
    }
    // Mark both this sender and its twin receiver with the current
    // "component" iteration number, a sort of generational code
    // to differentiate groups that never want each other.
    sender.component = sender.twin.component = component;
  }

  // Traverses edges and removes entries whose sender/receiver pair have
  // unequal component numbers, which indicates they aren't strongly connected
  Edge[] removeBadEdges(Edge[] edges) {
    int goodCount = 0;
    // First loop: count the number of matching component numbers
    for (Edge edge : edges) {
      if (edge.receiver.component == edge.sender.component)
        goodCount++;
    }
    if (goodCount == edges.length) return edges; // return if all edges are good

    // Populate the new array with only the good edges
    Edge[] goodEdges = new Edge[goodCount];
    goodCount = 0;
    for (Edge edge : edges) {
      if (edge.receiver.component == edge.sender.component)
        goodEdges[goodCount++] = edge;
    }
    return goodEdges;
  }

  // Remove unusable edges and resulting orphaned entries from the graph
  void removeImpossibleEdges() {
    assert frozen; // the graph should only be cleaned up once we are done adding things

    // We use the timestamp to flag items as visited. It needs to be advanced from
    // its default value of zero, which is also the unvisited flag value.
    advanceTimestamp();
    finished = new ArrayList<Vertex>(RECEIVERS.length);

    // We use Kosaraju's algorithm to determine which comopnents are strongly connected.
    // Strongly connected means every vertex is reachable from every other vertex.

    // The first loop determines the order for the second loop by placing vertices
    // in "finished" in the order that they point towards each other
    for (Vertex v : RECEIVERS)
      if (v.mark != timestamp) visitReceivers(v);
    // Reverse the list of senders such that they point in the direction we are
    // now traversing
    Collections.reverse(finished);
    for (Vertex v : finished) {
      if (v.mark != timestamp) {
        component++; // increment the strongly connected iteration count
        visitSenders(v); // visit the next group of senders
      }
    }

    // Now remove all edges between two different component counts
    for (Vertex v : RECEIVERS) {
      v.EDGES = removeBadEdges(v.EDGES);
    }
    for (Vertex v : SENDERS) {
      v.EDGES = removeBadEdges(v.EDGES);

      // Recalculate the lowest in cost, which may have changed when we
      // removed some edges
      long save = v.minimumInCost; // this line does nothing
      v.minimumInCost = Long.MAX_VALUE;
      for (Edge edge : v.EDGES)
        v.minimumInCost = Math.min(edge.cost,v.minimumInCost);
    }

    // Remove orphaned items, which are items no longer wanted by anybody
    // after culling bad edges. (It's not as sad as it sounds.)
    removeOrphans();
  }

  // Cull vertices that have no edges, except to themselves (receiver-sender pair)
  void removeOrphans() {
    // Count the number of vertices with at least one receiver
    int goodCount = 0;
    for (Vertex v : RECEIVERS) {
      if (v.EDGES.length > 1) goodCount++;
      else {
        assert v.EDGES.length == 1;         // there should always be at least one edge
        assert v.EDGES[0].sender == v.twin; // between the sender and receiver
        orphans.add(v);
      }
    }
    if (goodCount == RECEIVERS.length) return; // return if nothing is orphaned

    // Create a new array of viable entries
    Vertex[] receivers = new Vertex[goodCount];
    goodCount = 0;
    for (Vertex v : RECEIVERS) {
      if (v.EDGES.length > 1) receivers[goodCount++] = v;
    }
    RECEIVERS = receivers;
    Vertex[] senders = new Vertex[goodCount];
    goodCount = 0;
    for (Vertex v : SENDERS) {
      if (v.EDGES.length > 1) senders[goodCount++] = v;
    }
    SENDERS = senders;
  }

  //////////////////////////////////////////////////////////////////////

  Vertex sinkFrom; // designates the sending vertex (node) with the lowest cost
  long sinkCost;   // designates the cost of the cheapest sending vertex (node)

  static final long INFINITY = 100000000000000L; // 10^14

  void dijkstra() {
    sinkFrom = null;
    sinkCost = Long.MAX_VALUE;

    // Insert all vertices, both receiver and sender, into the heap
    Heap heap = new Heap();
    for (Vertex v : SENDERS) {
      v.from = null;
      // Give entry the highest cost
      v.heapEntry = heap.insert(v, INFINITY);
    }
    for (Vertex v : RECEIVERS) {
      v.from = null;
      // Give entry highest cost if unmatched, else lowest
      long cost = v.match == null ? 0 : INFINITY;
      v.heapEntry = heap.insert(v, cost);
    }

    while (!heap.isEmpty()) {
      // Grab the lowest cost entry's vertex and cost
      Heap.Entry minEntry = heap.extractMin();
      Vertex vertex = minEntry.vertex();
      long cost = minEntry.cost();

      if (cost == INFINITY) break; // everything left is unreachable

/* System.out.println(" "+vertex.name); */
      if (vertex.type == VertexType.RECEIVER) {
        for (Edge e : vertex.EDGES) {
          Vertex other = e.sender;
/* System.out.println("    "+vertex.name+"->"+other.name); */
          if (other == vertex.match) continue; // ignore item's current match
          // Price of receiver->sender is RecvPrice + edgeCost - SendPrice
          // Note: The SendPrice is typically the value of the sender's lowest edgeCost
          //       until all edges' vertices have been matched, then it's infinite.
          long c = vertex.price + e.cost - other.price;
          assert c >= 0; // per algorithm, all costs must be non-negative
          if (cost + c < other.heapEntry.cost()) {
            // We found a cheaper path between the vertex and this sender
            other.heapEntry.decreaseCost(cost + c);
            other.from = vertex;
          }
        }
      }
      else if (vertex.match == null) { // unmatched sender
        if (cost < sinkCost) {
          sinkFrom = vertex;
          sinkCost = cost;
        }
      }
      else { // matched sender
        Vertex other = vertex.match;
        // Price of sender->receiver is SendPrice + edgeCost - RecvPrice
        // Note: The RecvPrice is low until everything wanting the item is matched up
        long c = vertex.price - other.matchCost - other.price;
        assert c >= 0;
        if (cost + c < other.heapEntry.cost()) {
          other.heapEntry.decreaseCost(cost + c);
          other.from = vertex;
        }
      }
    }
  } // end dijkstra

  List<List<Vertex>> findCycles() {
    assert frozen; // graph analysis should only be performed when we are done adding things

    // Initialize all vertices
    for (Vertex v : RECEIVERS) {
      v.match = null;
      v.price = 0;
    }
    for (Vertex v : SENDERS) {
      v.match = null;
      v.price = v.minimumInCost;
    }

    for (int round = 0; round < RECEIVERS.length; round++) {
      dijkstra();

      // Update the matching
      Vertex sender = sinkFrom;
      assert sender != null;
      while (sender != null) {
        Vertex receiver = sender.from;

        // Unlink sender and receiver from current matches
        if (sender.match != null) sender.match.match = null;
        if (receiver.match != null) receiver.match.match = null;

        // Set the sender/receiver match to each other
        sender.match = receiver;
        receiver.match = sender;

        // Update matchCost
        for (Edge e : receiver.EDGES) { // iterate until we find the corresponding edge
          if (e.sender == sender) {
            receiver.matchCost = e.cost;
            break;
          }
        }

        sender = receiver.from; // evaluate the sender node this was connected to previously
      }

      // Update the prices
      for (Vertex v : RECEIVERS) v.price += v.heapEntry.cost();
      for (Vertex v : SENDERS)   v.price += v.heapEntry.cost();
    }

    // Bypass dummy entries that are matched and match the dummies to themselves
    elideDummies();

    advanceTimestamp();
    List<List<Vertex>> cycles = new ArrayList<List<Vertex>>();

    for (Vertex vertex : RECEIVERS) {
      if (vertex.mark == timestamp || vertex.match == vertex.twin) continue;

      List<Vertex> cycle = new ArrayList<Vertex>();
      Vertex v = vertex;
      while (v.mark != timestamp) {
        v.mark = timestamp;
        cycle.add(v);
        v = v.match.twin;
      }
      cycles.add(cycle);
    }
    return cycles;
  } // end findCycles

  //////////////////////////////////////////////////////////////////////

  private Random random = new Random();

  void setSeed(long seed) { random.setSeed(seed); }

  <T> void shuffle(T[] a) {
    for (int i = a.length; i > 1; i--) {
      int j = random.nextInt(i);
      T tmp = a[j];
      a[j] = a[i-1];
      a[i-1] = tmp;
    }
  }

  void shuffle() {
    shuffle(RECEIVERS);
    for (Vertex v : RECEIVERS) shuffle(v.EDGES);

    // shuffle senders also?
    //  for (int i = 0; i < RECEIVERS.length; i++) SENDERS[i] = RECEIVERS[i].twin;
    //  for (Vertex v : SENDERS) shuffle(v.EDGES);
  }

  // Bypass dummy entries that are matched and match the dummies to themselves
  void elideDummies() {
    for (Vertex v : RECEIVERS) {
      if (v.isDummy) continue;

      while (v.match.isDummy) {
        Vertex dummySender = v.match;
        Vertex nextSender = dummySender.twin.match;
        v.match = nextSender;
        nextSender.match = v;
        dummySender.match = dummySender.twin;
        dummySender.twin.match = dummySender;
      }
    }
  }

  void saveMatches() {
    for (Vertex v : RECEIVERS) {
      v.savedMatch = v.match;
      v.savedMatchCost = v.matchCost;
    }
    for (Vertex v : SENDERS) {
      v.savedMatch = v.match;
    }
  }
  void restoreMatches() {
    for (Vertex v : RECEIVERS) {
      v.match = v.savedMatch;
      v.matchCost = v.savedMatchCost;
    }
    for (Vertex v : SENDERS) {
      v.match = v.savedMatch;
    }
  }

} // end Graph
