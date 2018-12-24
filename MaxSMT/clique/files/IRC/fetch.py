import datetime
import os
import time

d = datetime.datetime(2004,7,5)
end_date=datetime.datetime.fromtimestamp(time.time())
delta = datetime.timedelta(days=1)
while d <= end_date:
    fname=d.strftime("logs/%Y-%m-%d.ubuntu.txt")
    cmd=d.strftime("http://irclogs.ubuntu.com/%Y/%m/%d/#ubuntu.txt").replace('#', '%23')
    print cmd
    os.system ("curl "+cmd+" > "+fname)
    d += delta
