// popup.js

document.addEventListener('DOMContentLoaded', function () {
    const trackedList = document.getElementById('tracked-list');
    const scanButton = document.getElementById('scan-page');
    const message = document.getElementById('message');

    function renderTrackedItems(items) {
        trackedList.innerHTML = '';
        items.forEach((item, index) => {
            const li = document.createElement('li');
            li.textContent = `${item.title} - $${item.price.toFixed(2)} `;

            const deleteBtn = document.createElement('button');
            deleteBtn.textContent = 'X';
            deleteBtn.style.marginLeft = '10px';
            deleteBtn.addEventListener('click', () => {
                items.splice(index, 1);
                chrome.storage.local.set({ trackedItems: items }, () => {
                    renderTrackedItems(items);
                    message.textContent = `Deleted: ${item.title}`;
                });
            });

            li.appendChild(deleteBtn);
            trackedList.appendChild(li);
        });
    }

    // Load tracked items on popup open
    chrome.storage.local.get({ trackedItems: [] }, (data) => {
        renderTrackedItems(data.trackedItems);
    });

    scanButton.addEventListener('click', () => {
        message.textContent = '';
        chrome.tabs.query({ active: true, currentWindow: true }, (tabs) => {
            if (!tabs || tabs.length === 0) {
                message.textContent = 'No active tab found.';
                return;
            }

            chrome.tabs.sendMessage(tabs[0].id, { action: 'scanPage' }, (response) => {
                console.log('Scan response:', response);

                if (!response || !response.url) {
                    message.textContent = 'No product found on this page.';
                    return;
                }

                chrome.storage.local.get({ trackedItems: [] }, (data) => {
                    const exists = data.trackedItems.some(item => item.url === response.url);
                    if (exists) {
                        message.textContent = 'This page is already tracked. Delete first to add again.';
                        return;
                    }

                    data.trackedItems.push(response);
                    chrome.storage.local.set({ trackedItems: data.trackedItems }, () => {
                        renderTrackedItems(data.trackedItems);
                        message.textContent = `Tracked: ${response.title}`;
                    });
                });
            });
        });
    });
});
