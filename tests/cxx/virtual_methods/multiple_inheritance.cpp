class Target;

class Source {
    Target *m_target;

    /*@
    predicate SourceOk() =
        this->m_target |-> ?t;

    predicate SourceDyn(std::type_info *dyn_type) =
        Source_vtype(this, dyn_type);
    @*/

public:
    Source() : m_target(nullptr)
    //@ requires true;
    //@ ensures SourceDyn(&typeid(Source)) &*& SourceOk();
    {}

    virtual ~Source()
    //@ requires SourceDyn(thisType) &*& SourceOk();
    //@ ensures true;
    {}

    virtual void setTarget(Target *target)
    //@ requires SourceOk();
    //@ ensures SourceOk();
    {
        m_target = target;
    }
};

class Target {
    Source *m_source;

    /*@
    predicate TargetOk() =
        this->m_source |-> ?s;

    predicate TargetDyn(std::type_info *dyn_type) =
        Target_vtype(this, dyn_type);
    @*/

public:
    Target() : m_source(nullptr)
    //@ requires true;
    //@ ensures TargetDyn(&typeid(Target)) &*& TargetOk();
    {}

    virtual ~Target()
    //@ requires TargetDyn(thisType) &*& TargetOk();
    //@ ensures true;
    {}  

    virtual void setSource(Source *source)
    //@ requires TargetOk();
    //@ ensures TargetOk();
    {
        m_source = source;
    } 
};

class Node : public Source, public Target {
    /*@
    predicate SourceOk() =
        Node_bases_constructed(this) &*&
        this->SourceOk(&typeid(Source))() &*&
        this->TargetOk(&typeid(Target))();
        
    predicate TargetOk() =
    	this->SourceOk(&typeid(Node))();

    predicate SourceDyn(std::type_info *dyn_type) =
        this->SourceDyn(&typeid(Source))(dyn_type) &*&
        this->TargetDyn(&typeid(Target))(dyn_type);
        
    predicate TargetDyn(std::type_info *dyn_type) =
    	this->SourceDyn(&typeid(Node))(dyn_type);
    @*/

public:
    Node()
    //@ requires true;
    //@ ensures SourceDyn(&typeid(Node)) &*& SourceOk();
    {
      setTarget(this);
      //@ close TargetOk();
      setSource(this);
      //@ open Node_vtype(this, &typeid(Node));
    }

    virtual ~Node()
    //@ requires SourceDyn(thisType) &*& SourceOk();
    //@ ensures true;
    {
      //@ close Node_vtype(this, &typeid(Node));
    }

    virtual void setTarget(Target *target)
    //@ requires SourceOk();
    //@ ensures SourceOk();
    {
        Source::setTarget(target);
    }

    virtual void setSource(Source *source)
    //@ requires TargetOk();
    //@ ensures TargetOk();
    {
        Target::setSource(source);
    }
};

int main()
//@ requires true;
//@ ensures true;
{
  Node *n = new Node();
  Source *s = n;
  //@ upcast_new_block((struct Source *) n);
  delete s;
}