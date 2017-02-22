import global_router as gr
import detail_router as dr
import sys
import time

f = None
if len(sys.argv) == 2:
    f = sys.argv[1]
else:
    raise ValueError('usage: demo.py <your path>/<example>.dot')

print('PNR for {}'.format(f))
routes, place_time, route_time = gr.test(f, (6,6))
start_dr = time.time()
dr.detailed_route(routes, 4)
end_dr = time.time()
dr_time = end_dr-start_dr
print('Detailed routing took {} seconds'.format(dr_time))
