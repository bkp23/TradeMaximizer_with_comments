// Priority queues implemented as pairing heaps

public class Heap {

  public boolean isEmpty() {
    return root == null;
  }

  public Entry extractMin() {
    assert root != null;
    Entry minEntry = root;
    root.used = true;
    Entry list = root.child;
    if (list != null) {
      // The (new) root can't have any siblings, so we re-merge them
      while (list.sibling != null) {
        Entry nextList = null;
        while (list != null && list.sibling != null) {
          Entry a = list;
          Entry b = a.sibling;
          list = b.sibling;

          // link a and b and add result to nextList
          a.sibling = b.sibling = null;
          a = merge(a,b);
          a.sibling = nextList;
          nextList = a;
        }
        if (list == null) list = nextList;
        else list.sibling = nextList;
      }
      list.prev = null; // separate this from the old root
    }
    root = list;
    return minEntry; // return the old root (the smallest value)
  }

  // Create a new entry and merge it into root
  public Entry insert(Graph.Vertex vertex,long cost) {
    Entry entry = new Entry(vertex,cost);
    root = root==null ? entry : merge(entry,root);
    return entry;
  }

  /* Entry is the type of nodes in the skew heap.
   * The insert method returns the new Entry object, so that the user can
   * later call the decreaseCost method.
   */
  public class Entry {
    public Graph.Vertex vertex() { return vertex; }
    public long cost() { return cost; }

    public void decreaseCost(long toCost) {
      assert !used;
      assert toCost < cost;
      cost = toCost;

      // Do we need to move this node? If not, then we're done
      if (this == root || cost >= prev.cost) return;

      // Detach node from prev
      if (this == prev.child) prev.child = sibling;
      else {
        assert this == prev.sibling; // if this isn't prev's child, it must be the sibling
        prev.sibling = sibling;
      }
      if (sibling != null) sibling.prev = prev;
      prev = null;

      root = merge(this,root);
    }

    private Graph.Vertex vertex; // the vertex with which this entry is associated
    private long cost; // the current cost of the vertex in the dijkstra algorithm

    private Entry child = null;
    private Entry sibling = null;
    private Entry prev = null; // parent if first child, else previous sibling

    private boolean used = false; // flag for marking the entry as removed from the heap

    private Entry(Graph.Vertex vertex,long cost) {
      this.vertex = vertex;
      this.cost = cost;
    }

    private Entry() {} // hide the default constructor
  }

  private Entry root = null;

  private Entry merge(Entry a,Entry b) {
    assert a != null && b != null; // check parameter validity

    // Make sure that a's root <= b's root, swap if necessary
    if (b.cost < a.cost) { Entry tmp = a; a = b; b = tmp; }

    // Add b to a's children
    b.prev = a;
    b.sibling = a.child;
    if (b.sibling != null) b.sibling.prev = b;
    a.child = b;

    return a;
  }

  //////////////////////////////////////////////////////////////////////
  // simple testing until we get a real testing framework...
  public static void main(String[] args) {
    long[] nums = new long[20];
    for (int i = 0; i < 20; i++) nums[i] = (long)(Math.random() * 100L);

    Heap h = new Heap();
    java.util.List<Heap.Entry> list =
        new java.util.ArrayList<Heap.Entry>();
    for (int i = 0; i < 20; i++) list.add( h.insert(null,nums[i]) );

    list.get(5).decreaseCost(nums[5] -= 10);
    list.get(10).decreaseCost(nums[10] -= 10);
    list.get(15).decreaseCost(nums[15] -= 10);

    while (!h.isEmpty())
      System.out.print(h.extractMin().cost() + " ");
    System.out.println();

    java.util.Arrays.sort(nums);
    for (long x : nums) System.out.print(x + " ");
    System.out.println();
  }

} // end Heap
