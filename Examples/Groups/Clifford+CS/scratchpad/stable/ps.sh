#!/bin/bash
ps aux --sort=-rss | grep -i '[a]gda' | head -3 | awk '{print $2, $6/1024 " MB", $10}'
