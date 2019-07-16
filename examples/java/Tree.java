package tree;

/*@
predicate tree(Tree t,bintree b) =
  switch(b){
    case tnil: return t==null;
    case tcons(a,bl,br): return t.value |-> ?v &*& t.left |-> ?l &*& t.right |-> ?r
			&*& tree(l,bl) &*& tree(r,br) &*& t!=null &*& a==v ;
  }&*& inorder(b)==true;

inductive bintree = |tnil |tcons(int,bintree,bintree);

fixpoint boolean t_contains(bintree b, int v) {
  switch (b) {
    case tnil: return false;
    case tcons(a,l,r): return (a==v ? true: (v < a? t_contains(l,v):t_contains(r,v)));
  }
}
fixpoint bintree tree_add(bintree b, int x) {
  switch (b) {
    case tnil: return tcons(x,tnil,tnil);
    case tcons(v,l,r): return x < v? tcons(v,tree_add(l,x),r):
			(x==v? tcons(v,l,r):tcons(v,l,tree_add(r,x)));
  }
}
fixpoint int max(bintree b){
  switch(b){
    case tcons(a,bl,br): return (br==tnil? a:max(br));
    case tnil: return 0;
  }
}
fixpoint int min(bintree b){
  switch(b){
    case tcons(a,bl,br): return (bl==tnil? a:min(bl));
    case tnil: return 0;
  }
}
fixpoint bintree tree_rem(bintree b, int x) {
  switch (b) {
    case tcons(v,l,r): return l==tnil&&r==tnil&&x==v? tnil:
			(x==v&&l==tnil? r:
			(x==v&&r==tnil? l:
			(x==v? tcons(max(l),tree_rem(l,max(l)),r):
			x < v? tcons(v,tree_rem(l,x),r):tcons(v,l,tree_rem(r,x)) ))) ;
    case tnil: return tnil;
  }
}
fixpoint boolean inorder(bintree b){
  switch(b){
	case tnil: return true;
	case tcons(a,bl,br): return (bl==tnil? true:max(bl) < a)&& (br==tnil? true: a < min(br))
		&& inorder(bl) && inorder(br);
  }
}
lemma void min_le_max(bintree b)
  requires inorder(b)==true &*& b!=tnil;
  ensures min(b)<=max(b);
{
  switch(b){
        case tnil:
	case tcons(v,l,r):if(l!=tnil||r!=tnil){
			   if(l==tnil){
			     min_le_max(r);
			   }else{
			     if(r!=tnil){
			       min_le_max(r);
			     }
			     min_le_max(l);
			   }
			}
  }
}
lemma void contains_max(bintree r)
  requires r!=tnil && inorder(r)==true;
  ensures t_contains(r,max(r))==true;
{
  switch(r){
	case tnil:
	case tcons(a,b,c):if(c!=tnil){
			   min_le_max(c);
			   contains_max(c);
			 }
  }
}
lemma void contains_min(bintree r)
  requires r!=tnil &*& inorder(r)==true;
  ensures t_contains(r,min(r))==true;
{
  switch(r){
	case tnil:
	case tcons(a,b,c):if(b!=tnil){
			 min_le_max(b);
			 contains_min(b);
			 }
  }
}
lemma void max_conj_add(bintree l,int v,int x)
  requires x < v &*& (max(l) < v||l==tnil) &*& inorder(l)==true;
  ensures max(tree_add(l,x)) < v &*& inorder(l)==true;
{
  switch(l){
	case tnil:
	case tcons(a,b,c):if(x < a){
			  max_conj_add(b,a,x);
			 }
			 if(a < x){
			  max_conj_add(c,v,x);
			 }
  }
}
lemma void min_conj_add(bintree r,int v,int x)
  requires v < x &*& (v < min(r)||r==tnil) &*& inorder(r)==true;
  ensures v < min(tree_add(r,x)) &*& inorder(r)==true;
{
  switch(r){
	case tnil:
	case tcons(a,b,c):if(a < x){
			  min_conj_add(c,a,x);
			 }
			 if(x < a){
			  min_conj_add(b,v,x);
			 }
  }
}
lemma void max_conj_rem(bintree l,int v,int x)
  requires x < v &*& (max(l) < v||l==tnil) &*& inorder(l)==true;
  ensures (max(tree_rem(l,x)) < v||tree_rem(l,x)==tnil) &*& inorder(l)==true;
{
  switch(l){
	case tnil:
	case tcons(a,b,c):if(x < a){
			  max_conj_rem(b,a,x);
			 }
			 if(a < x){
			  max_conj_rem(c,v,x);
			 }
  }
}

lemma void tree_add_inorder(bintree b, int x)
    requires inorder(b)==true &*& t_contains(b,x)==false;
    ensures inorder(tree_add(b,x))==true &*& t_contains(tree_add(b,x),x)==true;
{
    switch (b) {
        case tnil:
        case tcons(v,l,r):if(x < v){
			  max_conj_add(l,v,x);
			  tree_add_inorder(l,x);
			 }
			 if(v < x){
			  min_conj_add(r,v,x);
			  tree_add_inorder(r,x);
		  	 }
    }
}
lemma void min_all(bintree r,int x)
  requires t_contains(r,x)==true &*& inorder(r)==true;
  ensures min(r)<=x;
{
  switch(r){
	case tnil:
	case tcons(a,b,c):if(b!=tnil){
			   contains_max(b);
			   min_all(b,max(b));
			 }
			 if(t_contains(b,x)){
			   min_all(b,x);
			 }
  }
}
lemma void max_all(bintree r,int x)
  requires inorder(r)==true &*& t_contains(r,x)==true &*& x!=max(r);
  ensures x < max(r);
{
  switch(r){
	case tnil:
	case tcons(a,b,c):if(c!=tnil){
			   contains_min(c);
			   min_le_max(c);
			 }
			 if(t_contains(c,x)){
			   max_all(c,x);
			 }
  }
}
lemma void min_conj_rem(bintree r,int v,int x)
  requires v < x &*& (v < min(r)||r==tnil) &*& inorder(r)==true;
  ensures (v < min(tree_rem(r,x))||tree_rem(r,x)==tnil) &*& inorder(r)==true;
{
  switch(r){
	case tnil:
	case tcons(a,b,c):if(a < x){
			  min_conj_rem(c,a,x);
			 }
			 if(x < a){
			  min_conj_rem(b,v,x);
			 }
			 if(b!=tnil&&c!=tnil){
			  contains_max(b);
			  min_all(b,max(b));
			  min_conj_rem(b,v,max(b));
			 }
  }
}
lemma void contains_rem_max(bintree b)
  requires inorder(b)==true &*& b!=tnil &*& tree_rem(b,max(b))!=tnil &*& inorder(tree_rem(b,max(b)))==true;
  ensures t_contains(b,max(tree_rem(b,max(b))))==true;
{
  switch (b) {
        case tnil:
        case tcons(v,l,r):if(l==tnil||r!=tnil){
			   if(tree_rem(r,max(r))==tnil){
			     min_le_max(r);
		  	     contains_max(tree_rem(b,max(b)));
			   }else{
			     min_le_max(r);
			     if(v!=max(tree_rem(b,max(b)))){
			       max_all(tree_rem(b,max(b)),v);
			     }
			     contains_rem_max(r);
			   }
			 }else{
			   contains_max(tree_rem(b,max(b)));
			 }
  }
}
lemma void tree_rem_inorder(bintree b, int x)
    requires inorder(b)==true &*& t_contains(b,x)==true;
    ensures inorder(tree_rem(b,x))==true&*& t_contains(tree_rem(b,x),x)==false;
{
    switch (b) {
        case tnil:
        case tcons(v,l,r):if(x < v){
			  max_conj_rem(l,v,x);
			  tree_rem_inorder(l,x);
			 }
		  	 if(v < x){
			  min_conj_rem(r,v,x);
			  tree_rem_inorder(r,x);
			 }
			 if(x==v){
				if(l==tnil && r!=tnil){
					if(t_contains(r,x)==false){
					  contains_min(r);
					}else{
					  min_all(r,x);
					}
				}if(r==tnil&&l!=tnil){
					if(t_contains(l,x)==false){
					  contains_min(l);
					}else{
					  max_all(l,x);
					}
				}if(r!=tnil&&l!=tnil){
				   if(tree_rem(l,max(l))!=tnil){
				     contains_max(l);
				     tree_rem_inorder(l,max(l));
				     contains_rem_max(l);
				     if(max(l)!=max(tree_rem(l,max(l)))){
				       max_all(l,max(tree_rem(l,max(l))));
				       if(t_contains(r,x)==false){
				         contains_min(r);
				       }else{
				         min_all(r,x);
				       }
				     }else{
				       contains_max(tree_rem(l,max(l)));
				     }
				   }else{
				     if(t_contains(r,x)==false){
				       contains_min(r);
				     }else{
				       min_all(r,x);
				     }
				   }	
			    }
		  	}
  }
}
@*/
public class Tree{
	public int value;
	public Tree left;
	public Tree right;

	public Tree(int x)
	//@ requires true;
	//@ ensures tree(this,tcons(x,tnil,tnil));
	{
	    	this.value=x;
		this.left=null;
		this.right=null;
		//@ Tree l = this.left;
		//@ close tree(l,tnil);
		//@ Tree r = this.right;
		//@ close tree(r,tnil);
		//@ close tree(this,tcons(x,tnil,tnil));
	}
	public boolean contains(int x)
	//@ requires tree(this,?b);
	//@ ensures tree(this,b) &*& result==t_contains(b,x);
	{
		if(this==null){
			//@ open tree(this,b);
			//@ close tree(this,tnil);
			return false;
		}else{
			//@ open tree(this,b);
			int v=this.value;
			Tree l=this.left;
			Tree r=this.right;
			if(v==x){
				//@close tree(this,b);
				return true;
			}else{
				if(x < v){
					boolean temp1=false;
					if(l != null) {
					  temp1 = l.contains(x);
					} else {
					  //@ open tree(l, ?lv);
					  //@ close tree(l, lv);
					}
					//@close tree(this,b);
					return temp1;
				}else{
					boolean temp2=false;
					if(r != null) {
					  temp2 = r.contains(x);
					} else {
					  //@ open tree(r, ?rv);
					  //@ close tree(r, rv);
					}
					//@close tree(this,b);
					return temp2;
				}
			}
		}
	}
	public void add(int x)
	//@ requires tree(this,?b) &*& b!=tnil &*& false==t_contains(b,x) &*& inorder(b)==true;
	//@ ensures tree(this,tree_add(b,x)) &*& inorder(tree_add(b,x))==true;
	{
		//@ open tree(this,b);
		int v=this.value;
		Tree l=this.left;
		//@ open tree(l,?bl);
		//@ close tree(l,bl);
		Tree r=this.right;
		//@ open tree(r,?br);
		//@ close tree(r,br);
		if(x < v){
			if(l!=null){
				l.add(x);
				//@ tree_add_inorder(b,x);
				//@ close tree(this,tcons(v,tree_add(bl,x),br));
			}else{
				Tree temp=new Tree(x);
				this.left=temp;
				//@ open tree(l,bl);
				//@ close tree(this,tcons(v,tcons(x,tnil,tnil),br));
				//@ tree_add_inorder(b,x);
			}
		}else{
			if(v < x){
				if(r!=null){
					r.add(x);
					//@ tree_add_inorder(b,x);
					//@ close tree(this,tcons(v,bl,tree_add(br,x)));	
				}else{
					Tree temp=new Tree(x);
					this.right=temp;
					//@ open tree(r,br);
					//@ close tree(this,tcons(v,bl,tcons(x,tnil,tnil)));
				}
			}
		}
	}
	public int maximum()
	//@ requires tree(this,?b) &*& b!=tnil &*& inorder(b)==true;
	//@ ensures result==max(b) &*& tree(this,b);
	{
		//@ open tree(this,b);
		int v=this.value;
		Tree r=this.right;
		//@ open tree(r,?br);
		//@ close tree(r,br);
		if(r==null){
			//@ close tree(this,b);
			return v;
		}else{
			int m= r.maximum();
			//@ close tree(this,b);
			return m;
		}
	}
	public Tree remove(int x)
	//@ requires tree(this,?b) &*& b!=tnil &*& true==t_contains(b,x)  &*& inorder(b)==true;
	//@ ensures tree(result,tree_rem(b,x))&*& inorder(tree_rem(b,x))==true &*& false==t_contains(tree_rem(b,x),x);
	{
		//@ open tree(this,b);
		int v=this.value;
		Tree l=this.left;
		//@ open tree(l,?bl);
		//@ close tree(l,bl);
		Tree r=this.right;
		//@ open tree(r,?br);
		//@ close tree(r,br);
		//@ tree_rem_inorder(b,x);
		if(x < v){
			if(l!=null){
				Tree temp=l.remove(x);
				this.left=temp;
				//@ close tree(this,tcons(v,tree_rem(bl,x),br));
				return this;
			}
		}
		if(v < x){
			if(r!=null){
				Tree temp=r.remove(x);
				this.right=temp;
				//@ close tree(this,tcons(v,bl,tree_rem(br,x)));
				return this;
			}
		}
		if(v==x){
			if(l!=null&&r==null){
				//@ open tree(r,tnil);
				return l;
			}
			if(l==null&&r==null){
				//@ close tree(this,b);
				//@ close tree(null,tnil);
				return null;
			}
			if(l==null&&r!=null){
				//@ open tree(l,tnil);
				return r;
			}
			if(l!=null&&r!=null){
				Tree temp=null;
				int m=l.maximum();
				this.value=m;
				//@ contains_max(bl);
				temp=l.remove(m);
				this.left=temp;
				//@ close tree(this,tcons(m,tree_rem(bl,m),br));
				return this;
			}
		}
		//this return statement is necessary because javac can't tell that this code will never be reached
		return null;
	}
	public static void main(String[]  args)
	//@ requires true;
	//@ ensures true;
	{
		Tree t1=null;
		Tree t2=null;
		Tree t3=null;
		boolean a=false;
		boolean b=false;
		boolean c=false;
		boolean d=false;
		boolean e=false;
		boolean f=false;

		t1 = new Tree(3);
		b=t1.contains(2);
		assert(!b);
		t1.add(2);

		a=t1.contains(2);
		assert(a);
		c=t1.contains(3);
		assert(c);
		t2=t1.remove(3);
		if(t2 != null) {
		  d= t2.contains(3);
		  assert(!d);

		  t2.add(3);
		  e= t2.contains(2);
		  assert(e);
		  t3=t2.remove(3);
		  if(t3 != null) {
		    f=t3.contains(3);
		    assert(!f);
		  }
		}
	}
}
