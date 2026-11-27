"""Univariate evaluation and formal differentiation of a lifted label circuit."""
class StreamRing:
    def __init__(self,field,h):
        self.field=field
        self.size=h+1
        self.zero=(0,)*self.size
        self.one=(1,)+self.zero[1:]

    def add(self,x,y):
        return tuple(a^b for a,b in zip(x,y))

    def scalar(self,c):
        return (c,)+self.zero[1:]

    def scale(self,c,x):
        return tuple(self.field.mul(c,v) for v in x)

    def unit_inverse(self,x):
        # Lift the exact gate used by the square-zero circuit.
        inv=self.field.inverse(x[0])
        return self.scale(self.field.mul(inv,inv),x)

    def mul(self,x,y):
        result=[0]*self.size
        for i,u in enumerate(x):
            if u:
                for j in range(self.size-i):
                    if y[j]:
                        result[i+j]^=self.field.mul(u,y[j])
        return tuple(result)


class DualRing(StreamRing):
    def __init__(self,base):
        self.base=base
        self.field=base.field
        self.size=2*base.size
        self.zero=base.zero+base.zero
        self.one=base.one+base.zero

    def mul(self,x,y):
        n=self.base.size
        a,b=x[:n],x[n:]
        c,d=y[:n],y[n:]
        return self.base.mul(a,c)+self.base.add(self.base.mul(a,d),self.base.mul(b,c))
