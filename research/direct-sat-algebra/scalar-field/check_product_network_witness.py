from unittest.mock import patch
import check_product_network_inequality as controls
from hidden_product_network import Chart
from product_network_witness import witness, choose_parameters
from affine_binomial import power
from punctured_witness import BinaryField
from quadratic_image import evaluate

def check(field,frames,shift,edges,offset,target,form,required=1):
    chart=Chart(field,tuple(map(tuple,frames)),shift,tuple(edges),offset)
    x=witness(chart,target,form,required)
    if x is not None:
        assert evaluate((form,),x)==required
    return x is not None

with patch.object(controls,'decide',check):
    controls.explicit()
    controls.hidden()
field=BinaryField(19)
for target in range(1,16):
    poly={(i,):power(field,target,(-i)%15) for i in range(15)}
    assert choose_parameters(field,[15],poly)==[target]
print('26 witness decisions with lifted raw bits, plus 15 singleton multiplicative hits')
