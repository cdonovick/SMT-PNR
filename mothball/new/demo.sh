#run demo file
python demo.py ../examples/NMS_10_reduce.dot
#convert .dot file to .png
dot -Kneato -n -Tpng -o display.png display.dot
